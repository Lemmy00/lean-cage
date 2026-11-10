(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual repeated EOF iteration retains its bytes and caller
   roots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayFramedRuntime GatewaySourcePaths
  GatewayThreadRuntime GatewayRuntimeABI GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayStreamLayout GatewayStreamRelations
  GatewayReadonly GatewayPrimitiveCalls GatewayBufferReference GatewayTransferMath GatewaySendRuntime GatewaySendReady
  GatewayReadyBindings GatewayReadyComplete GatewayReadyOutgoing GatewayExchangeSetup GatewayExchangeTransport GatewayEOFNative
  GatewayEOFSource GatewayEOFLoopReady GatewayEOFReceiveSource GatewayEOFReceive GatewayEOFEvent.
Import ListNotations.
Open Scope Z_scope.

Section EOFIteration.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
  (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
  (held:gateway_eof_receive_runtime backend io native stable discipline).
Variables(stream extra:Values.block)(readonly:Values.block->Z->Prop)(reference:mem)(owner:World).
Local Definition context initial:=gateway_owned_buffer_context native stable discipline stream extra Ptrofs.zero Ptrofs.zero
  initial 1 readonly reference owner None.
Local Lemma context_closed initial:gateway_ambient_closed backend(context initial).
Proof. apply gateway_owned_buffer_context_ambient with(io:=io)(thread_errno:=thread_errno);exact thread. Qed.

Theorem actual_eof_loop_receive allocation_before allocated environment temporaries initial
    before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_extra=Some(extra,tuchar)->
  stream_descriptor initial<>stream_control initial->context initial before world->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current updated count bytes,
    events=prefix++suffix /\-1<=count<=1 /\Z.of_nat(length bytes)=Z.max 0 count /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries before)world)prefix
      (gateway_live(Returnstate(Vlong(Int64.repr count))
        (exchange_eof_receive_cont environment(exchange_eof_receive_temps(stream_descriptor updated)temporaries))memory)current) /\
    gateway_received_bytes io(stream_descriptor initial)prefix=bytes /\gateway_sent_bytes io(stream_descriptor initial)prefix=[] /\
    context updated memory current /\gateway_stream_transport_after initial updated /\
    Mem.loadbytes memory extra 0(Z.max 0 count)=Some(inj_bytes bytes) /\
    (count=0->exists observed,In(gateway_primitive observed)prefix /\
      io observed=Some(gateway_native_receive(stream_descriptor initial)1 0[])) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vlong(Int64.repr count))
        (exchange_eof_receive_cont environment(exchange_eof_receive_temps(stream_descriptor updated)temporaries))memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC STREAM EXTRA SEPARATE READY NONNULL RUN.
  assert(READY_LOCAL:environment!_host_ready=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(READY_FUNCTION:gateway_function_binding(Clight.globalenv prog)_host_ready(Internal f_host_ready)).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  assert(RECEIVE_LOCAL:environment!_recv=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(RECEIVE_FUNCTION:gateway_function_binding(Clight.globalenv prog)_recv gateway_receive_definition).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  destruct(actual_eof_loop_first_ready backend(Clight.globalenv prog)(context initial)(context_closed initial)environment temporaries stream
    before world events value after next STREAM READY_LOCAL READY_FUNCTION READY NONNULL RUN)
    as(p1&ready_body&r1&c1&cw1&m1&w1&E1&Q1&P1&C1&B1&S1).
  destruct(actual_ready_complete backend(Clight.globalenv prog)io native stable discipline thread_errno thread actual_gateway_ready_bindings
    stream Ptrofs.zero initial extra Ptrofs.zero 1 readonly Int.one c1 cw1 ready_body m1 w1(proj1 C1)B1)
    as(updated&RAW&TRANSPORT&BUFFER&NATIVE&READY_EMPTY).
  assert(C2:context updated m1 w1).
  { split;[exact RAW|]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2 C1))|exact BUFFER].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2 C1))|exact NATIVE]. }
  assert(READY_NO_SEND:gateway_sent_bytes io(stream_descriptor initial)ready_body=[]).
  { eapply(gateway_actual_ready_no_data_send backend(Clight.globalenv prog)io native stable discipline thread_errno thread actual_gateway_ready_bindings
      c1 cw1 stream Ptrofs.zero initial extra Ptrofs.zero 1 readonly Int.one ready_body m1 w1).
    - exact(proj1(proj1 C1)).
    - exact(proj1(proj2(proj1 C1))).
    - exact(proj1(proj2(proj2(proj1 C1)))).
    - exact(proj1(proj2(proj2(proj2(proj1 C1))))).
    - exact(proj2(proj2(proj2(proj2(proj1 C1))))).
    - exact SEPARATE.
    - left;reflexivity.
    - exact B1. }
  assert(CELLS:forall memory current,context updated memory current->gateway_stream_memory memory stream Ptrofs.zero updated).
  { intros memory current GOOD;exact(gateway_read_stream_cells _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2(proj1 GOOD)))))). }
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)gateway_receive_definition
    (exchange_eof_receive_arguments(stream_descriptor updated)extra)
    (exchange_eof_receive_cont environment(exchange_eof_receive_temps(stream_descriptor updated)temporaries))
    (context updated)_(context updated)
    (actual_eof_ready_receive_path backend(Clight.globalenv prog)(context updated)(context_closed updated)environment temporaries m1 stream updated extra
      STREAM EXTRA RECEIVE_LOCAL RECEIVE_FUNCTION(proj1 actual_stream_layout)CELLS)m1 w1 r1 value after next C2 S1)
    as(p2&r2&c2&cw2&E2&Q2&P2&C3&S2).
  cbn[gateway_replace_memory]in P2.
  destruct(gateway_return_cut backend(Clight.globalenv prog)gateway_receive_definition
    (exchange_eof_receive_arguments(stream_descriptor updated)extra)
    (exchange_eof_receive_cont environment(exchange_eof_receive_temps(stream_descriptor updated)temporaries))
    c2 cw2 r2(Returnstate value Kstop after)next I ltac:(cbn;lia)S2)
    as(receive_body&suffix&returned&memory&current&E3&B2&SUFFIX).
  destruct(actual_eof_receive_read_context backend io native stable discipline thread_errno thread held(Clight.globalenv prog)
    stream Ptrofs.zero updated extra Ptrofs.zero 1 readonly c2 cw2 receive_body returned memory current(proj1 C3)ltac:(lia)B2)
    as(count&bytes&COUNT&RETURNED&LENGTH&OBSERVED&LOADED&FINAL).
  subst returned.
  destruct(actual_eof_receive_owned_buffer backend io native stable discipline thread_errno thread held(Clight.globalenv prog)
    stream Ptrofs.zero updated extra Ptrofs.zero 1 readonly c2 cw2 receive_body(Vlong(Int64.repr count))memory current
    (proj1 C3)ltac:(lia)B2)as[FRAME CAPTURE].
  assert(C4:context updated memory current).
  { split;[exact FINAL|]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2 C3))|exact FRAME].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2 C3))|exact CAPTURE]. }
  exists(p1++ready_body++p2++receive_body),suffix,memory,current,updated,count,bytes.
  split;[rewrite E1,E2,E3;repeat rewrite<-app_assoc;reflexivity|]. split;[exact COUNT|]. split;[exact LENGTH|]. split.
  - eapply gateway_steps_append;[exact P1|].
    eapply gateway_steps_append;[exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(exchange_eof_ready_cont environment temporaries)I B1)|].
    eapply gateway_steps_append;[exact P2|exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _
      (exchange_eof_receive_cont environment(exchange_eof_receive_temps(stream_descriptor updated)temporaries))I B2)].
  - split.
    + rewrite !gateway_received_bytes_append,(gateway_quiet_received_empty io(stream_descriptor initial)p1 Q1),READY_EMPTY,
        (gateway_quiet_received_empty io(stream_descriptor initial)p2 Q2).
      rewrite<-(gateway_transport_descriptor initial updated TRANSPORT);exact OBSERVED.
    + split.
      * rewrite !gateway_sent_bytes_append,(gateway_quiet_sent_empty io(stream_descriptor initial)p1 Q1),READY_NO_SEND,
          (gateway_quiet_sent_empty io(stream_descriptor initial)p2 Q2).
        eapply actual_eof_receive_no_send;[exact thread|exact held|exact(proj1 C3)|lia|exact B2].
      * split;[exact C4|]. split;[exact TRANSPORT|]. split;[exact LOADED|]. split;[|exact SUFFIX].
        intro ZERO;subst count.
        destruct(actual_eof_receive_zero_event backend io native stable discipline thread_errno thread held
          (Clight.globalenv prog)stream updated extra readonly c2 cw2 receive_body memory current(proj1 C3)B2)
          as[observed[OCCURRENCE IO]].
        exists observed;split.
        -- apply in_or_app;right;apply in_or_app;right;apply in_or_app;right;exact OCCURRENCE.
        -- rewrite(gateway_transport_descriptor initial updated TRANSPORT)in IO;exact IO.
Qed.
End EOFIteration.
