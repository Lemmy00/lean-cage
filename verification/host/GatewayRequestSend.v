(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same successful original exchange sends its header and all original fields. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayReadonly GatewayRuntimeCuts
  GatewayThreadRuntime GatewayStreamInterface GatewayStreamRelations GatewayReadContext GatewayTransportFrame GatewaySendInterface
  GatewaySendRuntime GatewaySendState GatewayMemoryPrefixes GatewayFramedRuntime GatewayFieldStores
  GatewayHeaderTransfer GatewayHeaderComplete GatewayHeaderSuccess GatewayPayloadControl GatewayPayloadPaths GatewayPayloadMemory
  GatewayPayloadLoop GatewayExchangeTransport.
Import ListNotations.
Open Scope Z_scope.

Definition header_bound_temps(temporaries:temp_env):=
  PTree.set _failed(Vint Int.zero)(PTree.set _t'30(Vint Int.zero)temporaries).
Definition gateway_request_bytes command fault header_rows payload_rows:=
  gateway_complete_header command fault header_rows++gateway_payload_rows_bytes payload_rows 0 8.

Lemma actual_header_result_bind {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  gateway_memory_prefix backend ge
    (State f_host_exchange header_transfer_after Kstop environment(header_bound_temps temporaries)memory)property property
    (State f_host_exchange Sskip(Kseq header_transfer_bind(Kseq header_transfer_after Kstop))environment
      (PTree.set _t'30(Vint Int.zero)temporaries)memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange header_transfer_bind(Kseq header_transfer_after Kstop)
    environment(PTree.set _t'30(Vint Int.zero)temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq header_transfer_after Kstop)
    environment(header_bound_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss|].
  eapply gateway_memory_same with(following:=State f_host_exchange header_transfer_after Kstop
    environment(header_bound_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.

Section Request.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variables(stream header:Values.block)(readonly:Values.block->Z->Prop)(reference:mem)(origin:World)(initial:gateway_stream_values)
  (environment:env)(object:Values.block)(offset:ptrofs)(rows:nat->gateway_payload_row).
Hypotheses(STREAM:environment!_stream=Some(stream,Tstruct _host_stream noattr))
  (LOCAL:environment!_host_transfer=None)
  (FUNCTION:gateway_function_binding(Clight.globalenv prog)_host_transfer(Internal f_host_transfer))
  (SIZEOF:sizeof(genv_cenv(Clight.globalenv prog))(Tstruct _host_field noattr)=40)
  (DATA:field_member_layout(Clight.globalenv prog)_data 16)(SIZE:field_member_layout(Clight.globalenv prog)_size 8)
  (SPAN:Ptrofs.unsigned offset+320<=Ptrofs.modulus)(CELLS:gateway_payload_field_cells reference object offset rows)
  (COVER:forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)
  (PAYLOADS:gateway_payload_rows_readable readonly reference rows)
  (SEPARATE:stream_descriptor initial<>stream_control initial).
Local Definition sending:=gateway_sending_state native stable discipline stream readonly reference origin initial.
Local Lemma sending_closed:gateway_ambient_closed backend sending.
Proof. apply gateway_sending_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Theorem actual_exchange_request_send temporaries command fault header_rows before world events value after next:
  temporaries!_fields=Some(Vptr object offset)->sending before world->
  (forall position,0<=position<112->readonly header position)->
  Mem.loadbytes before header 0 112=Some(inj_bytes(gateway_complete_header command fault header_rows))->
  value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)
      (header_transfer_cont environment temporaries)before)world)events(gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)
        (header_transfer_cont environment temporaries)before)world)prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment final_temps memory)current) /\
    gateway_sent_bytes io(stream_descriptor initial)prefix=gateway_request_bytes command fault header_rows rows /\
    sending memory current /\final_temps!_failed=Some(Vint Int.zero) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros FIELDS READY HEADER_COVER HEADER_BYTES NONNULL RUN.
  destruct READY as[current_stream[RAW[TRANSPORT HISTORY]]].
  assert(CURRENT_SEPARATE:stream_descriptor current_stream<>stream_control current_stream).
  { unfold gateway_stream_transport_after in TRANSPORT;intuition congruence. }
  destruct(actual_successful_header_sends_ready backend io native stable discipline thread_errno runtime environment temporaries
    before world stream header current_stream readonly command fault header_rows events value after next
    (proj1 RAW)(proj1(proj2 RAW))(proj1(proj2(proj2(proj2 RAW))))(proj2(proj2(proj2(proj2 RAW))))
    HEADER_COVER HEADER_BYTES CURRENT_SEPARATE NONNULL RUN)
    as(p1 & r1 & m1 & w1 & E1 & BODY & S1 & OBSERVED & RECEIPT & SIDE & PRIVATE & STABLE).
  assert(R1:sending m1 w1).
  { eapply gateway_sending_after with(io:=io)(current:=current_stream).
    - exists current_stream;split;[exact RAW|split;assumption].
    - exact(proj2(proj2(proj2(proj2 RAW)))).
    - exact TRANSPORT.
    - exact RECEIPT.
    - exact SIDE.
    - exact PRIVATE.
    - exact STABLE. }
  destruct(gateway_uniform_edge_side_cut backend(Clight.globalenv prog)sending sending_closed
    (Returnstate(Vint Int.zero)(header_transfer_cont environment temporaries)m1)
    (State f_host_exchange Sskip(Kseq header_transfer_bind(Kseq header_transfer_after Kstop))environment
      (PTree.set _t'30(Vint Int.zero)temporaries)m1)
    m1 w1 r1 value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)R1 S1)
    as(p2 & r2 & m2 & w2 & E2 & Q2 & P2 & R2 & S2).
  cbn[gateway_replace_memory]in P2,S2.
  set(loop_temps:=PTree.set _index__1(Vint Int.zero)(header_bound_temps temporaries)).
  assert(SCRIPT:gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange payload_loop payload_loop_cont environment loop_temps m2)sending sending
    (State f_host_exchange Sskip(Kseq header_transfer_bind(Kseq header_transfer_after Kstop))environment
      (PTree.set _t'30(Vint Int.zero)temporaries)m2)).
  { eapply gateway_memory_prefix_compose.
    - apply actual_header_result_bind;exact sending_closed.
    - apply actual_payload_enter;exact sending_closed. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m2 w2 r2(Returnstate value Kstop after)next
    SCRIPT I R2 S2)as(p3 & r3 & m3 & w3 & E3 & Q3 & P3 & R3 & S3).
  cbn[gateway_replace_memory]in P3,S3.
  assert(LOOP_FIELDS:loop_temps!_fields=Some(Vptr object offset)).
  { unfold loop_temps,header_bound_temps;rewrite !PTree.gso by discriminate;exact FIELDS. }
  destruct(actual_payload_loop_bounded backend io native stable discipline thread_errno runtime stream readonly reference origin initial
    environment object offset rows STREAM LOCAL FUNCTION SIZEOF DATA SIZE SPAN CELLS COVER PAYLOADS SEPARATE 8 loop_temps 0
    m3 w3 r3 value after next eq_refl LOOP_FIELDS ltac:(unfold loop_temps;apply PTree.gss)
    ltac:(unfold loop_temps,header_bound_temps;rewrite PTree.gso by discriminate;apply PTree.gss)R3 NONNULL S3)
    as(p4 & suffix & memory & current & final_temps & E4 & P4 & OBSERVED4 & FINAL & FRAME & FAILED & SUFFIX).
  exists(p1++p2++gateway_source E0::(p3++p4)),suffix,memory,current,final_temps.
  split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;cbn[app];repeat rewrite<-app_assoc;reflexivity|].
  split.
  - eapply gateway_steps_append;[exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _
      (header_transfer_cont environment temporaries)I BODY)|].
    eapply gateway_steps_append;[exact P2|].
    econstructor;[apply gateway_internal;[cbn;tauto|constructor;reflexivity]|].
    eapply gateway_steps_append;[exact P3|exact P4].
  - split.
    + rewrite !gateway_sent_bytes_append.
      rewrite(gateway_pending_sent_empty io(stream_descriptor initial)p2).
      * change(gateway_sent_bytes io(stream_descriptor initial)p1++
          gateway_sent_bytes io(stream_descriptor initial)(p3++p4)=gateway_request_bytes command fault header_rows rows).
        rewrite gateway_sent_bytes_append,(gateway_quiet_sent_empty io(stream_descriptor initial)p3 Q3),OBSERVED4.
        rewrite<-(gateway_transport_descriptor initial current_stream TRANSPORT),OBSERVED;reflexivity.
      * eapply Forall_impl;[|exact Q2];intros event SAME;left;exact SAME.
    + split;[exact FINAL|]. split;assumption.
Qed.
End Request.
