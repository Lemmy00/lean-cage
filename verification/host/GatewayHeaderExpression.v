(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual descriptor expressions feed the same packet word calls. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess Writers CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayMemoryPrefixes
  GatewayFramedRuntime GatewayReadonly GatewayHeaderRuntime GatewayHeaderPacket GatewayHeaderCalls
  GatewayThreadRuntime GatewayStreamInterface GatewayContexts GatewayReturnFrontier GatewayWordReceipt GatewayHeaderBoundary.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Inductive gateway_packet_word:=gateway_packet32:int->gateway_packet_word|gateway_packet64:int64->gateway_packet_word.
Definition gateway_word_writer word:=match word with gateway_packet32 _=>gateway_header32|gateway_packet64 _=>gateway_header64 end.
Definition gateway_word_function word:=gateway_header_function(gateway_word_writer word).
Definition gateway_word_identifier word:=match word with gateway_packet32 _=>_host_put32|gateway_packet64 _=>_host_put64 end.
Definition gateway_word_value word:=match word with gateway_packet32 value=>Vint value|gateway_packet64 value=>Vlong value end.
Definition gateway_word_type word:=match word with gateway_packet32 _=>tuint|gateway_packet64 _=>tulong end.
Definition gateway_word_width word:nat:=match word with gateway_packet32 _=>4|gateway_packet64 _=>8 end.
Definition gateway_word_bytes word:=match word with
  gateway_packet32 value=>gateway_native_bytes(put32_values value)|gateway_packet64 value=>gateway_native_bytes(put64_values value)end.
Definition header_expression_statement word pointer scalar:=Scall None
  (Evar(gateway_word_identifier word)(Tfunction[tptr tuchar;gateway_word_type word]tvoid cc_default))[pointer;scalar].

Lemma actual_header_expression_call ge environment temporaries object offset word pointer scalar memory continuation:
  environment!(gateway_word_identifier word)=None->
  gateway_function_binding ge(gateway_word_identifier word)(Internal(gateway_word_function word))->
  expression_value ge environment temporaries memory pointer(Vptr object offset)->
  expression_value ge environment temporaries memory scalar(gateway_word_value word)->
  typeof pointer=tptr tuchar->typeof scalar=gateway_word_type word->
  store_edge ge(State f_host_exchange(header_expression_statement word pointer scalar)continuation environment temporaries memory)
    (Callstate(Internal(gateway_word_function word))[Vptr object offset;gateway_word_value word]
      (Kcall None f_host_exchange environment temporaries continuation)memory).
Proof.
  intros LOCAL[symbol[SYMBOL FUNCTION]]POINTER SCALAR POINTER_TYPE SCALAR_TYPE.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr object offset).
    + exact POINTER.
    + rewrite POINTER_TYPE;reflexivity.
    + eapply cons_argument_values with(v:=gateway_word_value word);
        [exact SCALAR|rewrite SCALAR_TYPE;destruct word;reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - destruct word;reflexivity.
Qed.

Section Expression.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge:Clight.genv.

Lemma gateway_header_packet_word mode object held readonly reference owner bytes word
    before world events returned after next:
  gateway_header_packet native stable discipline mode object held readonly reference owner bytes before world->
  (length bytes+gateway_word_width word<=112)%nat->
  (forall position,0<=position<112->~readonly object position)->
  gateway_steps backend ge
    (gateway_live(writer_initial(gateway_word_function word)object(Ptrofs.repr(Z.of_nat(length bytes)))
      (gateway_word_value word)Kstop before)world)events(gateway_live(Returnstate returned Kstop after)next)->
  returned=Vundef /\
  gateway_header_packet native stable discipline mode object held readonly reference owner(bytes++gateway_word_bytes word)after next /\
  Forall gateway_quiet_event events.
Proof. destruct word;[apply gateway_header_packet_put32 with(io:=io)(thread_errno:=thread_errno)
  |apply gateway_header_packet_put64 with(io:=io)(thread_errno:=thread_errno)];exact runtime. Qed.

Variables(mode:option val)(object:Values.block)(held:list Values.block)(readonly:Values.block->Z->Prop)
  (reference:mem)(owner:World)(environment:env)(temporaries:temp_env).
Hypothesis DISJOINT:forall position,0<=position<112->~readonly object position.
Local Definition packet bytes:=gateway_header_packet native stable discipline mode object held readonly reference owner bytes.
Local Lemma packet_closed bytes:gateway_ambient_closed backend(packet bytes).
Proof. apply gateway_header_packet_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Theorem actual_header_expression_before_boundary outer word pointer scalar bytes before world events terminal next:
  gateway_header_boundary terminal->typeof pointer=tptr tuchar->typeof scalar=gateway_word_type word->
  environment!(gateway_word_identifier word)=None->
  gateway_function_binding ge(gateway_word_identifier word)(Internal(gateway_word_function word))->
  (forall memory current,packet bytes memory current->expression_value ge environment temporaries memory pointer
    (Vptr object(Ptrofs.repr(Z.of_nat(length bytes)))))->
  (forall memory current,packet bytes memory current->expression_value ge environment temporaries memory scalar(gateway_word_value word))->
  (length bytes+gateway_word_width word<=112)%nat->packet bytes before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange(header_expression_statement word pointer scalar)
      outer environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(header_expression_statement word pointer scalar)
        outer environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange Sskip outer environment temporaries memory)current) /\
    packet(bytes++gateway_word_bytes word)memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange Sskip outer environment temporaries memory)current)suffix
      (gateway_live terminal next).
Proof.
  intros BOUNDARY POINTER_TYPE SCALAR_TYPE LOCAL FUNCTION POINTER SCALAR SPACE READY RUN.
  assert(SCRIPT:gateway_memory_prefix backend ge
    (Callstate(Internal(gateway_word_function word))[Vptr object(Ptrofs.repr(Z.of_nat(length bytes)));gateway_word_value word]
      (Kcall None f_host_exchange environment temporaries outer)before)
    (packet bytes)(packet bytes)
    (State f_host_exchange(header_expression_statement word pointer scalar)outer environment temporaries before)).
  { eapply gateway_memory_same with(following:=Callstate(Internal(gateway_word_function word))
      [Vptr object(Ptrofs.repr(Z.of_nat(length bytes)));gateway_word_value word]
      (Kcall None f_host_exchange environment temporaries outer)before).
    - apply packet_closed.
    - cbn;tauto.
    - intros available current GOOD;eapply actual_header_expression_call;
        [exact LOCAL|exact FUNCTION|apply POINTER with(current:=current);exact GOOD
        |apply SCALAR with(current:=current);exact GOOD|exact POINTER_TYPE|exact SCALAR_TYPE].
    - apply gateway_memory_identity. }
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ before world events
    terminal next SCRIPT(gateway_header_boundary_instruction terminal BOUNDARY)READY RUN)
    as(pending & tail & called & called_world & EVENTS1 & QUIET1 & PREFIX1 & CALLED & TAIL).
  cbn[gateway_replace_memory]in PREFIX1,TAIL.
  destruct(gateway_header_boundary_return_cut backend ge(gateway_word_writer word)
    [Vptr object(Ptrofs.repr(Z.of_nat(length bytes)));gateway_word_value word]
    f_host_exchange environment temporaries outer called called_world tail terminal next BOUNDARY TAIL)
    as(body & returned_tail & returned & returned_memory & returned_world & EVENTS2 & BODY & AFTER_BODY).
  destruct(gateway_header_packet_word mode object held readonly reference owner bytes word
    called called_world body returned returned_memory returned_world CALLED SPACE DISJOINT BODY)
    as[RETURNED[PACKET QUIET2]];subst returned.
  pose proof(gateway_plug_steps backend ge _ _ _ (Kcall None f_host_exchange environment temporaries outer)I BODY)
    as PLUG;cbn[gateway_plug plug_state]in PLUG.
  destruct(gateway_header_caller_return_cut backend ge(packet(bytes++gateway_word_bytes word))
    (packet_closed _)Vundef f_host_exchange environment temporaries outer
    returned_memory returned_world returned_tail terminal next BOUNDARY PACKET AFTER_BODY)
    as(ambient & suffix & memory & current & EVENTS3 & AMBIENT & PREFIX3 & FINAL & SUFFIX).
  exists(pending++body++ambient++[gateway_source E0]),suffix,memory,current.
  split.
  - rewrite EVENTS1,EVENTS2,EVENTS3;repeat rewrite<-app_assoc;reflexivity.
  - split.
    + apply Forall_app;split;[exact QUIET1|].
      apply Forall_app;split;[exact QUIET2|].
      apply Forall_app;split.
      * eapply Forall_impl;[|exact AMBIENT];intros event SAME;right;exact SAME.
      * repeat constructor.
    + split.
      * eapply gateway_steps_append;[exact PREFIX1|].
        eapply gateway_steps_append;[exact PLUG|].
        eapply gateway_steps_append;[exact PREFIX3|].
        econstructor;[apply gateway_internal;[cbn;tauto|constructor;exact I]|constructor].
      * split;assumption.
Qed.

Theorem actual_header_expression_before_transfer outer word pointer scalar bytes before world events arguments continuation after next:
  typeof pointer=tptr tuchar->typeof scalar=gateway_word_type word->
  environment!(gateway_word_identifier word)=None->
  gateway_function_binding ge(gateway_word_identifier word)(Internal(gateway_word_function word))->
  (forall memory current,packet bytes memory current->expression_value ge environment temporaries memory pointer
    (Vptr object(Ptrofs.repr(Z.of_nat(length bytes)))))->
  (forall memory current,packet bytes memory current->expression_value ge environment temporaries memory scalar(gateway_word_value word))->
  (length bytes+gateway_word_width word<=112)%nat->packet bytes before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange(header_expression_statement word pointer scalar)
      outer environment temporaries before)world)events
    (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(header_expression_statement word pointer scalar)
        outer environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange Sskip outer environment temporaries memory)current) /\
    packet(bytes++gateway_word_bytes word)memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange Sskip outer environment temporaries memory)current)suffix
      (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next).
Proof.
  intros;eapply actual_header_expression_before_boundary;try eassumption;reflexivity.
Qed.
End Expression.
