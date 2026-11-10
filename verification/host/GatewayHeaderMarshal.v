(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real command and field calls encode retained packet words. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess Writers CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayMemoryPrefixes
  GatewayFramedRuntime GatewayReadonly GatewayHeaderRuntime GatewayHeaderPacket GatewayHeaderCalls
  GatewayHeaderInitialization GatewayThreadRuntime GatewayStreamInterface GatewayContexts
  GatewayReturnFrontier GatewayWordReceipt GatewayWordData GatewayHeaderBoundary.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition header_pointer_expr offset:=Ebinop Oadd(Evar _header(tarray tuchar 112))
  (Econst_int(Int.repr offset)tint)(tptr tuchar).
Definition header_word32_statement offset identifier:=Scall None
  (Evar _host_put32(Tfunction[tptr tuchar;tuint]tvoid cc_default))
  [header_pointer_expr offset;Etempvar identifier tuint].
Definition header_word64_statement offset identifier:=Scall None
  (Evar _host_put64(Tfunction[tptr tuchar;tulong]tvoid cc_default))
  [header_pointer_expr offset;Etempvar identifier tulong].

Lemma actual_header_pointer_value ge environment temporaries memory object offset:
  environment!_header=Some(object,tarray tuchar 112)->0<=offset<=112->
  expression_value ge environment temporaries memory(header_pointer_expr offset)(Vptr object(Ptrofs.repr offset)).
Proof.
  intros ARRAY OFFSET;unfold header_pointer_expr;eapply binary_expression_value.
  - eapply location_read_value;[apply local_location_value;exact ARRAY|].
    apply deref_loc_reference;reflexivity.
  - apply old_expression_value;constructor.
  - change(Some(Vptr object(Ptrofs.add Ptrofs.zero
      (Ptrofs.mul(Ptrofs.repr 1)(Ptrofs.of_ints(Int.repr offset)))))=Some(Vptr object(Ptrofs.repr offset))).
    rewrite Ptrofs.mul_commut,Ptrofs.mul_one,Ptrofs.add_zero_l.
    unfold Ptrofs.of_ints;rewrite Int.signed_repr;[reflexivity|].
    change Int.min_signed with(-2147483648);change Int.max_signed with 2147483647;lia.
Qed.

Lemma actual_header_put32_call ge environment temporaries object offset identifier value memory continuation:
  environment!_header=Some(object,tarray tuchar 112)->0<=offset<=112->
  environment!_host_put32=None->gateway_function_binding ge _host_put32(Internal f_host_put32)->
  temporaries!identifier=Some(Vint value)->
  store_edge ge(State f_host_exchange(header_word32_statement offset identifier)continuation environment temporaries memory)
    (Callstate(Internal f_host_put32)[Vptr object(Ptrofs.repr offset);Vint value]
      (Kcall None f_host_exchange environment temporaries continuation)memory).
Proof.
  intros ARRAY OFFSET LOCAL[symbol[SYMBOL FUNCTION]]VALUE.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr object(Ptrofs.repr offset)).
    + apply actual_header_pointer_value;assumption.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint value);
        [apply old_expression_value,value_temp;exact VALUE|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_header_put64_call ge environment temporaries object offset identifier value memory continuation:
  environment!_header=Some(object,tarray tuchar 112)->0<=offset<=112->
  environment!_host_put64=None->gateway_function_binding ge _host_put64(Internal f_host_put64)->
  temporaries!identifier=Some(Vlong value)->
  store_edge ge(State f_host_exchange(header_word64_statement offset identifier)continuation environment temporaries memory)
    (Callstate(Internal f_host_put64)[Vptr object(Ptrofs.repr offset);Vlong value]
      (Kcall None f_host_exchange environment temporaries continuation)memory).
Proof.
  intros ARRAY OFFSET LOCAL[symbol[SYMBOL FUNCTION]]VALUE.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr object(Ptrofs.repr offset)).
    + apply actual_header_pointer_value;assumption.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vlong value);
        [apply old_expression_value,value_temp;exact VALUE|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Section Marshal.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge:Clight.genv.
Variables(mode:option val)(object:Values.block)(held:list Values.block)(readonly:Values.block->Z->Prop)
  (reference:mem)(owner:World)(environment:env)(temporaries:temp_env).
Hypothesis ARRAY:environment!_header=Some(object,tarray tuchar 112).
Hypothesis DISJOINT:forall position,0<=position<112->~readonly object position.
Local Definition packet bytes:=gateway_header_packet native stable discipline mode object held readonly reference owner bytes.
Local Lemma packet_closed bytes:gateway_ambient_closed backend(packet bytes).
Proof. apply gateway_header_packet_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Theorem actual_header_put32_before_boundary rest identifier value bytes before world events terminal next:
  gateway_header_boundary terminal->environment!_host_put32=None->gateway_function_binding ge _host_put32(Internal f_host_put32)->
  temporaries!identifier=Some(Vint value)->(length bytes+4<=112)%nat->packet bytes before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange(Ssequence(header_word32_statement(Z.of_nat(length bytes))identifier)rest)
      Kstop environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(Ssequence(header_word32_statement(Z.of_nat(length bytes))identifier)rest)
        Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange rest Kstop environment temporaries memory)current) /\
    packet(bytes++gateway_native_bytes(put32_values value))memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange rest Kstop environment temporaries memory)current)suffix
      (gateway_live terminal next).
Proof.
  intros BOUNDARY LOCAL FUNCTION VALUE SPACE READY RUN.
  assert(SCRIPT:gateway_memory_prefix backend ge
    (Callstate(Internal f_host_put32)[Vptr object(Ptrofs.repr(Z.of_nat(length bytes)));Vint value]
      (Kcall None f_host_exchange environment temporaries(Kseq rest Kstop))before)
    (packet bytes)(packet bytes)
    (State f_host_exchange(Ssequence(header_word32_statement(Z.of_nat(length bytes))identifier)rest)
      Kstop environment temporaries before)).
  { eapply gateway_memory_same with(following:=State f_host_exchange
      (header_word32_statement(Z.of_nat(length bytes))identifier)(Kseq rest Kstop)environment temporaries before);
      [apply packet_closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_memory_same with(following:=Callstate(Internal f_host_put32)
      [Vptr object(Ptrofs.repr(Z.of_nat(length bytes)));Vint value]
      (Kcall None f_host_exchange environment temporaries(Kseq rest Kstop))before).
    - apply packet_closed.
    - cbn;tauto.
    - intros available current GOOD;eapply actual_header_put32_call;
        [exact ARRAY|lia|exact LOCAL|exact FUNCTION|exact VALUE].
    - apply gateway_memory_identity. }
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ before world events
    terminal next SCRIPT(gateway_header_boundary_instruction terminal BOUNDARY)READY RUN)
    as(pending & tail & called & called_world & EVENTS1 & QUIET1 & PREFIX1 & CALLED & TAIL).
  cbn[gateway_replace_memory]in PREFIX1,TAIL.
  destruct(gateway_header_boundary_return_cut backend ge gateway_header32
    [Vptr object(Ptrofs.repr(Z.of_nat(length bytes)));Vint value]
    f_host_exchange environment temporaries(Kseq rest Kstop)called called_world tail terminal next BOUNDARY TAIL)
    as(body & returned_tail & returned & returned_memory & returned_world & EVENTS2 & BODY & AFTER_BODY).
  destruct(gateway_header_packet_put32 backend io native stable discipline thread_errno runtime ge
    mode object held readonly reference owner bytes value called called_world body returned returned_memory returned_world
    CALLED SPACE DISJOINT BODY)as[RETURNED[PACKET QUIET2]];subst returned.
  pose proof(gateway_plug_steps backend ge _ _ _ (Kcall None f_host_exchange environment temporaries(Kseq rest Kstop))I BODY)
    as PLUG;cbn[gateway_plug plug_state]in PLUG.
  destruct(gateway_header_caller_return_cut backend ge
    (packet(bytes++gateway_native_bytes(put32_values value)))
    (packet_closed _)Vundef f_host_exchange environment temporaries(Kseq rest Kstop)
    returned_memory returned_world returned_tail terminal next BOUNDARY PACKET AFTER_BODY)
    as(ambient & after_return & result_memory & result_world & EVENTS3 & AMBIENT & PREFIX3 & RESULT & AFTER_RETURN).
  assert(SKIP:gateway_memory_prefix backend ge(State f_host_exchange rest Kstop environment temporaries result_memory)
    (packet(bytes++gateway_native_bytes(put32_values value)))
    (packet(bytes++gateway_native_bytes(put32_values value)))
    (State f_host_exchange Sskip(Kseq rest Kstop)environment temporaries result_memory)).
  { eapply gateway_memory_same with(following:=State f_host_exchange rest Kstop environment temporaries result_memory);
      [apply packet_closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity]. }
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ result_memory result_world after_return
    terminal next SKIP(gateway_header_boundary_instruction terminal BOUNDARY)RESULT AFTER_RETURN)
    as(skip & suffix & memory & current & EVENTS4 & QUIET4 & PREFIX4 & FINAL & SUFFIX).
  cbn[gateway_replace_memory]in PREFIX4,SUFFIX.
  exists(pending++body++ambient++gateway_source E0::skip),suffix,memory,current.
  split.
  - rewrite EVENTS1,EVENTS2,EVENTS3,EVENTS4;repeat rewrite<-app_assoc;reflexivity.
  - split.
    + apply Forall_app;split;[exact QUIET1|].
      apply Forall_app;split;[exact QUIET2|].
      apply Forall_app;split.
      * eapply Forall_impl;[|exact AMBIENT];intros event SAME;right;exact SAME.
      * constructor;[left;reflexivity|exact QUIET4].
    + split.
      * eapply gateway_steps_append;[exact PREFIX1|].
        eapply gateway_steps_append;[exact PLUG|].
        eapply gateway_steps_append;[exact PREFIX3|].
        econstructor;[apply gateway_internal;[cbn;tauto|constructor;exact I]|exact PREFIX4].
      * split;assumption.
Qed.

Theorem actual_header_put32_before_transfer rest identifier value bytes before world events arguments continuation after next:
  environment!_host_put32=None->gateway_function_binding ge _host_put32(Internal f_host_put32)->
  temporaries!identifier=Some(Vint value)->(length bytes+4<=112)%nat->packet bytes before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange(Ssequence(header_word32_statement(Z.of_nat(length bytes))identifier)rest)
      Kstop environment temporaries before)world)events
    (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(Ssequence(header_word32_statement(Z.of_nat(length bytes))identifier)rest)
        Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange rest Kstop environment temporaries memory)current) /\
    packet(bytes++gateway_native_bytes(put32_values value))memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange rest Kstop environment temporaries memory)current)suffix
      (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next).
Proof. intros;eapply actual_header_put32_before_boundary;try eassumption;reflexivity. Qed.
End Marshal.
