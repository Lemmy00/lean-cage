(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each actual payload iteration sends its original field bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayReadonly
  GatewayRuntimeCuts GatewayMemoryPrefixes GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayStreamRelations GatewayReadContext GatewayTransportFrame GatewaySendState GatewaySendRuntime GatewaySendInterface
  GatewayFieldStores GatewayPayloadControl GatewayPayloadReturn GatewayPayloadPaths GatewayPayloadMemory GatewayPayloadSend.
Import ListNotations.
Open Scope Z_scope.

Definition payload_iteration_temps temporaries index pointer size:=
  payload_next_temps(payload_call_temps(payload_guard_temps temporaries)pointer size)index.

Section Iteration.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variables(stream:Values.block)(readonly:Values.block->Z->Prop)(reference:mem)(origin:World)(initial:gateway_stream_values)
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

Theorem actual_payload_iteration temporaries index before world events value after next:
  (index<8)%nat->temporaries!_fields=Some(Vptr object offset)->
  temporaries!_index__1=Some(Vint(Int.repr(Z.of_nat index)))->temporaries!_failed=Some(Vint Int.zero)->
  sending before world->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange payload_loop payload_loop_cont environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange payload_loop payload_loop_cont environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange payload_loop payload_loop_cont environment
        (payload_iteration_temps temporaries index(gateway_payload_pointer(rows index))(gateway_payload_size(rows index)))memory)current) /\
    gateway_sent_bytes io(stream_descriptor initial)prefix=gateway_payload_bytes(rows index) /\sending memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange payload_loop payload_loop_cont environment
        (payload_iteration_temps temporaries index(gateway_payload_pointer(rows index))(gateway_payload_size(rows index)))memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros BOUND FIELDS INDEX FAILED READY NONNULL RUN.
  set(pointer:=gateway_payload_pointer(rows index)).
  set(size:=gateway_payload_size(rows index)).
  destruct(PAYLOADS index BOUND)as[ADDRESS[PAYLOAD_COVER PAYLOAD_BYTES]].
  set(guarded:=payload_guard_temps temporaries).
  assert(GUARD_FIELDS:guarded!_fields=Some(Vptr object offset)).
  { unfold guarded,payload_guard_temps;rewrite PTree.gso by discriminate;exact FIELDS. }
  assert(GUARD_INDEX:guarded!_index__1=Some(Vint(Int.repr(Z.of_nat index)))).
  { unfold guarded,payload_guard_temps;rewrite PTree.gso by discriminate;exact INDEX. }
  assert(DATA_VALUE:forall memory current,sending memory current->
    expression_value(Clight.globalenv prog)environment guarded memory payload_data_expression pointer).
  { intros memory current GOOD;eapply gateway_payload_current_data;
      [exact SIZEOF|exact DATA|exact GUARD_FIELDS|exact GUARD_INDEX|exact BOUND|exact SPAN|exact CELLS|exact COVER|exact GOOD]. }
  assert(SIZE_VALUE:forall memory current,sending memory current->
    expression_value(Clight.globalenv prog)environment(payload_data_temps guarded pointer)memory payload_size_expression(Vlong size)).
  { intros memory current GOOD;eapply gateway_payload_current_size;
      [exact SIZEOF|exact SIZE|unfold payload_data_temps;rewrite PTree.gso by discriminate;exact GUARD_FIELDS
      |unfold payload_data_temps;rewrite PTree.gso by discriminate;exact GUARD_INDEX
      |exact BOUND|exact SPAN|exact CELLS|exact COVER|exact GOOD]. }
  set(called_temps:=payload_call_temps guarded pointer size).
  assert(CALL_INDEX:called_temps!_index__1=Some(Vint(Int.repr(Z.of_nat index)))).
  { unfold called_temps,payload_call_temps,payload_data_temps;rewrite !PTree.gso by discriminate;exact GUARD_INDEX. }
  assert(SCRIPT:gateway_memory_prefix backend(Clight.globalenv prog)
    (Callstate(Internal f_host_transfer)(payload_transfer_arguments stream pointer size)
      (payload_transfer_cont environment called_temps)before)sending sending
    (State f_host_exchange payload_loop payload_loop_cont environment temporaries before)).
  { eapply gateway_memory_prefix_compose.
    - exact(actual_payload_guard_path backend(Clight.globalenv prog)sending sending_closed environment temporaries before index
        BOUND FAILED INDEX).
    - eapply gateway_memory_prefix_compose.
      + exact(actual_payload_fields_path backend(Clight.globalenv prog)sending sending_closed environment guarded before pointer size
          DATA_VALUE SIZE_VALUE).
      + eapply gateway_memory_same with(following:=Callstate(Internal f_host_transfer)(payload_transfer_arguments stream pointer size)
          (payload_transfer_cont environment called_temps)before).
        * exact sending_closed.
        * cbn;tauto.
        * intros memory current GOOD;apply actual_payload_transfer_call;
            [exact STREAM|exact LOCAL|exact FUNCTION
            |unfold called_temps,payload_call_temps,payload_data_temps;rewrite PTree.gso by discriminate;apply PTree.gss
            |unfold called_temps,payload_call_temps;apply PTree.gss|apply gateway_payload_address_cast;exact ADDRESS].
        * apply gateway_memory_identity. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events
    (Returnstate value Kstop after)next SCRIPT I READY RUN)
    as(p1 & r1 & m1 & w1 & E1 & Q1 & P1 & R1 & S1).
  cbn[gateway_replace_memory]in P1,S1.
  destruct R1 as[current_stream[RAW[TRANSPORT HISTORY]]].
  assert(CURRENT_BYTES:gateway_sent_payload m1 pointer(Int64.unsigned size)(gateway_payload_bytes(rows index))).
  { eapply gateway_payload_bytes_retained;[exact PAYLOAD_COVER|exact PAYLOAD_BYTES|
      exact(gateway_transport_readonly _ _ _ _ _ _ _ _ _ _ _ HISTORY)]. }
  assert(CURRENT_SEPARATE:stream_descriptor current_stream<>stream_control current_stream).
  { unfold gateway_stream_transport_after in TRANSPORT;intuition congruence. }
  destruct(actual_successful_payload_sends backend io native stable discipline thread_errno runtime environment called_temps
    (Int.repr(Z.of_nat index))m1 w1 stream current_stream readonly pointer size(gateway_payload_bytes(rows index))r1 value after next
    CALL_INDEX(proj1 RAW)(proj1(proj2 RAW))(proj1(proj2(proj2(proj2 RAW))))
    (proj2(proj2(proj2(proj2 RAW))))PAYLOAD_COVER CURRENT_BYTES CURRENT_SEPARATE NONNULL S1)
    as(p2 & r2 & m2 & w2 & E2 & BODY & S2 & OBSERVED & RECEIPT & SIDE & PRIVATE & STABLE).
  assert(R2:sending m2 w2).
  { eapply gateway_sending_after with(io:=io)(current:=current_stream).
    - exists current_stream;split;[exact RAW|split;assumption].
    - exact(proj2(proj2(proj2(proj2 RAW)))).
    - exact TRANSPORT.
    - exact RECEIPT.
    - exact SIDE.
    - exact PRIVATE.
    - exact STABLE. }
  destruct(gateway_uniform_edge_side_cut backend(Clight.globalenv prog)sending sending_closed
    (Returnstate(Vint Int.zero)(payload_transfer_cont environment called_temps)m2)
    (State f_host_exchange Sskip(Kseq payload_bind_failed payload_iteration_cont)environment
      (PTree.set _t'32(Vint Int.zero)called_temps)m2)
    m2 w2 r2 value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)R2 S2)
    as(p3 & r3 & m3 & w3 & E3 & Q3 & P3 & R3 & S3).
  cbn[gateway_replace_memory]in P3,S3.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m3 w3 r3(Returnstate value Kstop after)next
    (actual_payload_increment_path backend(Clight.globalenv prog)sending sending_closed environment called_temps m3 index BOUND CALL_INDEX)
    I R3 S3)as(p4 & suffix & memory & current & E4 & Q4 & P4 & FINAL & SUFFIX).
  cbn[gateway_replace_memory]in P4,SUFFIX.
  exists(p1++p2++p3++gateway_source E0::p4),suffix,memory,current.
  split.
  - rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;reflexivity.
  - split.
    + eapply gateway_steps_append;[exact P1|].
      eapply gateway_steps_append;[exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _
        (payload_transfer_cont environment called_temps)I BODY)|].
      eapply gateway_steps_append;[exact P3|].
      econstructor;[apply gateway_internal;[cbn;tauto|constructor;reflexivity]|exact P4].
    + split.
      * rewrite !gateway_sent_bytes_append,(gateway_quiet_sent_empty io(stream_descriptor initial)p1 Q1).
        rewrite(gateway_pending_sent_empty io(stream_descriptor initial)p3).
        -- change(gateway_sent_bytes io(stream_descriptor initial)p2++gateway_sent_bytes io(stream_descriptor initial)p4=
             gateway_payload_bytes(rows index)).
           rewrite(gateway_quiet_sent_empty io(stream_descriptor initial)p4 Q4),app_nil_r,
             <-(gateway_transport_descriptor initial current_stream TRANSPORT);exact OBSERVED.
        -- eapply Forall_impl;[|exact Q3];intros event SAME;left;exact SAME.
      * split;[exact FINAL|exact SUFFIX].
Qed.
End Iteration.
