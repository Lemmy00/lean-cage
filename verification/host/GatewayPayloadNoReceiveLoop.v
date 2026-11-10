(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The complete real payload loop leaves response bytes unread. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayReadonly GatewayThreadRuntime GatewayStreamInterface
  GatewayReadContext GatewayStreamRelations GatewayMemoryPrefixes GatewayFramedRuntime GatewaySendState GatewaySendRuntime GatewayFieldStores
  GatewayPayloadControl GatewayPayloadPaths GatewayPayloadMemory GatewayPayloadIteration GatewayPayloadNoReceiveIteration GatewayPayloadLoop GatewayPrimitiveCalls GatewayTransferMath GatewayPayloadExit GatewayExchangeTransport.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
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

Theorem actual_payload_loop_no_receive remaining:
  forall temporaries index before world events value after next,
  (index+remaining=8)%nat->temporaries!_fields=Some(Vptr object offset)->
  temporaries!_index__1=Some(Vint(Int.repr(Z.of_nat index)))->temporaries!_failed=Some(Vint Int.zero)->
  sending before world->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange payload_loop payload_loop_cont environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange payload_loop payload_loop_cont environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment final_temps memory)current) /\
    gateway_sent_bytes io(stream_descriptor initial)prefix=gateway_payload_rows_bytes rows index remaining /\
    gateway_received_bytes io(stream_descriptor initial)prefix=[] /\sending memory current /\
    gateway_payload_temps_frame temporaries final_temps /\final_temps!_failed=Some(Vint Int.zero) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  induction remaining as[|remaining IH];intros temporaries index before world events value after next
    COUNT FIELDS INDEX FAILED READY NONNULL RUN.
  - assert(index=8)%nat by lia;subst index.
    destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events(Returnstate value Kstop after)next
      (actual_payload_exit_path backend(Clight.globalenv prog)sending sending_closed environment temporaries before FAILED INDEX)
      I READY RUN)as(prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & FINAL & SUFFIX).
    cbn[gateway_replace_memory]in PREFIX,SUFFIX.
    exists prefix,suffix,memory,current,(payload_exit_temps temporaries).
    split;[exact EVENTS|]. split;[exact PREFIX|]. split;[apply gateway_quiet_sent_empty;exact QUIET|].
    split;[apply gateway_quiet_received_empty;exact QUIET|]. split;[exact FINAL|].
    split.
    + intros identifier A B C D E F;unfold payload_exit_temps;rewrite PTree.gso by congruence;reflexivity.
    + split;[unfold payload_exit_temps;rewrite PTree.gso by discriminate;exact FAILED|exact SUFFIX].
  - assert(BOUND:(index<8)%nat)by lia.
    destruct(actual_payload_iteration_no_receive backend io native stable discipline thread_errno runtime stream readonly reference origin initial
      environment object offset rows STREAM LOCAL FUNCTION SIZEOF DATA SIZE SPAN CELLS COVER PAYLOADS SEPARATE
      temporaries index before world events value after next BOUND FIELDS INDEX FAILED READY NONNULL RUN)
      as(first & rest & middle & middle_world & EVENTS1 & FIRST & OBSERVED & NO_RECEIVE & MIDDLE & REST).
    set(temps:=payload_iteration_temps temporaries index(gateway_payload_pointer(rows index))(gateway_payload_size(rows index))).
    assert(NEXT_FIELDS:temps!_fields=Some(Vptr object offset)).
    { unfold temps,payload_iteration_temps,payload_next_temps,payload_call_temps,payload_data_temps,payload_guard_temps;
        rewrite !PTree.gso by discriminate;exact FIELDS. }
    assert(NEXT_INDEX:temps!_index__1=Some(Vint(Int.repr(Z.of_nat(S index))))).
    { unfold temps,payload_iteration_temps,payload_next_temps;apply PTree.gss. }
    assert(NEXT_FAILED:temps!_failed=Some(Vint Int.zero)).
    { unfold temps,payload_iteration_temps,payload_next_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
    destruct(IH temps(S index)middle middle_world rest value after next ltac:(lia)NEXT_FIELDS NEXT_INDEX NEXT_FAILED MIDDLE NONNULL REST)
      as(second & suffix & memory & current & final_temps & EVENTS2 & SECOND & OBSERVED2 & NO_RECEIVE2 & FINAL & FRAME & FAILED2 & SUFFIX).
    exists(first++second),suffix,memory,current,final_temps.
    split;[rewrite EVENTS1,EVENTS2,app_assoc;reflexivity|].
    split;[eapply gateway_steps_append;[exact FIRST|exact SECOND]|].
    split;[rewrite gateway_sent_bytes_append,OBSERVED,OBSERVED2;reflexivity|].
    split;[rewrite gateway_received_bytes_append,NO_RECEIVE,NO_RECEIVE2;reflexivity|]. split;[exact FINAL|].
    split.
    + intros identifier A B C D E F;rewrite(FRAME identifier A B C D E F).
      apply gateway_payload_iteration_frame;assumption.
    + split;assumption.
Qed.
End Loop.
