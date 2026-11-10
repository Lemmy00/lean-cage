(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Half-close retains the actual response buffer and interpreter state. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayReadContext GatewaySendRuntime GatewayReadonly GatewayExchangeABI GatewayExchangeRuntime GatewayPrimitiveCalls GatewayPrimitiveQuiet.
Import ListNotations.
Local Open Scope string_scope.

Theorem actual_shutdown_receive_context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (exchange:gateway_exchange_runtime backend io native stable discipline)
    stream response initial readonly descriptor before world events returned after next:
  gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate gateway_shutdown_definition[Vint descriptor;Vint Int.one]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  (returned=Vint Int.zero\/returned=Vint(Int.neg Int.one)) /\
  gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly after next /\
  gateway_received_bytes io(stream_descriptor initial)events=[] /\
  gateway_sent_bytes io(stream_descriptor initial)events=[].
Proof.
  intros READY RUN.
  set(context:=gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly).
  assert(CLOSED:gateway_runtime_discipline backend context).
  { exact(gateway_read_context_ambient backend io native stable discipline thread_errno runtime None stream Ptrofs.zero initial
      response Ptrofs.zero 24 readonly). }
  assert(EFFECT:forall memory current result changed future observed,context memory current->
    gateway_external backend(EF_external "shutdown"(mksignature[Xint;Xint]Xint cc_default))[tint;tint]tint cc_default
      [Vint descriptor;Vint Int.one]memory current result changed future observed->
    (result=Vint Int.zero\/result=Vint(Int.neg Int.one)) /\context changed future).
  { intros memory current result changed future observed CALLED OPERATION.
    destruct(gateway_shutdown_operation backend io native stable discipline exchange memory current descriptor result changed future observed
      (proj1 CALLED)OPERATION)as[TYPE[SIDE[ACCESS[FRAME IO]]]].
    split;[exact TYPE|]. eapply gateway_read_context_preserved;[exact CALLED|exact SIDE|exact ACCESS|exact FRAME]. }
  destruct(gateway_actual_primitive_context backend(Clight.globalenv prog)
    (EF_external "shutdown"(mksignature[Xint;Xint]Xint cc_default))[tint;tint]tint cc_default[Vint descriptor;Vint Int.one]
    context(fun result memory current=>(result=Vint Int.zero\/result=Vint(Int.neg Int.one)) /\context memory current)CLOSED
    ltac:(intros result memory current changed future[TYPE INPUT]INTERFERENCE;split;[exact TYPE|eapply CLOSED;eassumption])
    EFFECT before world events returned after next READY RUN)
    as(prefix&suffix&memory&current&changed&future&observed&EVENTS&PENDING&PREFIX&CALLED&OPERATION&OUTPUT&SUFFIX&FINAL).
  destruct(gateway_shutdown_operation backend io native stable discipline exchange memory current descriptor returned changed future observed
    (proj1 CALLED)OPERATION)as[TYPE[SIDE[ACCESS[FRAME IO]]]].
  split;[exact(proj1 FINAL)|]. split;[exact(proj2 FINAL)|].
  eapply gateway_external_no_io_projection;[exact EVENTS|exact PENDING|exact IO|exact SUFFIX].
Qed.
