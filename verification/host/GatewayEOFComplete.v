(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The original successful response reaches cleanup through actual
   EOF. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayReadContext GatewayStreamInterface
  GatewayStreamRelations GatewayReadonly GatewayPrimitiveCalls GatewaySendRuntime GatewayBufferReference GatewayTransferMath
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayExchangeTransport GatewayEOFNative GatewayEOFSource GatewayEOFLoop.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_eof_entry_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory object offset:
  temporaries!_result=Some(Vptr object offset)->
  (forall before world,property before world->Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)=true)->
  gateway_memory_prefix backend ge
    (State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries memory)property property
    (State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries memory).
Proof.
  intros RESULT POINTER.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_phase exchange_eof_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto| |apply gateway_memory_identity].
  intros before world READY;apply certified_if_edge with(v:=Vptr object offset)(b:=true).
  - apply old_expression_value,value_temp;exact RESULT.
  - change((if Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)then Some true else None)=Some true).
    rewrite(POINTER before world READY);reflexivity.
Qed.

Theorem actual_exchange_successful_eof {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (held:gateway_eof_receive_runtime backend io native stable discipline)
    stream extra readonly allocation_before allocated environment temporaries initial object offset
    before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_extra=Some(extra,tuchar)->
  temporaries!_result=Some(Vptr object offset)->
  (forall memory current,discipline None memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true)->
  stream_descriptor initial<>stream_control initial->
  gateway_read_context native stable discipline None stream Ptrofs.zero initial extra Ptrofs.zero 1 readonly before world->
  value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current final_temps updated observed,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current) /\
    gateway_owned_buffer_context native stable discipline stream extra Ptrofs.zero Ptrofs.zero updated 1 readonly before world None memory current /\
    gateway_stream_transport_after initial updated /\final_temps!_result=Some(Vptr object offset) /\
    gateway_received_bytes io(stream_descriptor initial)prefix=[] /\gateway_sent_bytes io(stream_descriptor initial)prefix=[] /\
    In(gateway_primitive observed)prefix /\io observed=Some(gateway_native_receive(stream_descriptor initial)1 0[]) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC STREAM EXTRA RESULT POINTER SEPARATE READY NONNULL RUN.
  set(context:=gateway_owned_buffer_context native stable discipline stream extra Ptrofs.zero Ptrofs.zero initial 1 readonly before world None).
  assert(CLOSED:gateway_ambient_closed backend context).
  { apply gateway_owned_buffer_context_ambient with(io:=io)(thread_errno:=thread_errno);exact thread. }
  assert(INITIAL:context before world).
  { split;[exact READY|]. split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events(Returnstate value Kstop after)next
    (actual_eof_entry_path backend(Clight.globalenv prog)context CLOSED environment temporaries before object offset RESULT
      ltac:(intros memory current INPUT;exact(POINTER memory current(proj1(proj1 INPUT)))))I INITIAL RUN)
    as(p1&r1&m1&w1&E1&Q1&P1&C1&S1).
  cbn[gateway_replace_memory]in P1,S1.
  destruct(actual_eof_loop_complete backend io native stable discipline thread_errno thread held stream extra readonly before world
    allocation_before allocated environment ALLOC STREAM EXTRA temporaries initial m1 w1 r1 value after next SEPARATE C1 NONNULL S1)
    as(p2&suffix&memory&current&final_temps&updated&observed&E2&P2&FINAL&TRANSPORT&RESULT2&READ2&SEND2&EOF2&IO2&SUFFIX).
  exists(p1++p2),suffix,memory,current,final_temps,updated,observed.
  split;[rewrite E1,E2,app_assoc;reflexivity|]. split;[eapply gateway_steps_append;[exact P1|exact P2]|].
  split;[exact FINAL|]. split;[exact TRANSPORT|]. split;[rewrite RESULT2;exact RESULT|]. split.
  - rewrite gateway_received_bytes_append,(gateway_quiet_received_empty io(stream_descriptor initial)p1 Q1),READ2;reflexivity.
  - split.
    + rewrite gateway_sent_bytes_append,(gateway_quiet_sent_empty io(stream_descriptor initial)p1 Q1),SEND2;reflexivity.
    + split;[apply in_or_app;right;exact EOF2|]. split;assumption.
Qed.
