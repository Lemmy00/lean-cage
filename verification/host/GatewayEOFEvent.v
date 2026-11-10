(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Native EOF knowledge names the same actual zero-byte receive
   event. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayThreadRuntime GatewayReadContext GatewayStreamInterface GatewayReceiveRuntime GatewayEOFNative.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_eof_receive_zero_event {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (held:gateway_eof_receive_runtime backend io native stable discipline)
    ge stream initial data readonly before world events after next:
  gateway_read_context native stable discipline None stream Ptrofs.zero initial data Ptrofs.zero 1 readonly before world->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data Ptrofs.zero;Vlong Int64.one;Vint Int.zero]Kstop before)world)events
    (gateway_live(Returnstate(Vlong Int64.zero)Kstop after)next)->
  exists observed,In(gateway_primitive observed)events /\
    io observed=Some(gateway_native_receive(stream_descriptor initial)1 0[]).
Proof.
  intros READY RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world events(Vlong Int64.zero)after next RUN)
    as(prefix&suffix&called&called_world&changed&changed_world&observed&EVENTS&PENDING&PREFIX&OPERATION&SUFFIX).
  assert(CALLED:gateway_read_context native stable discipline None stream Ptrofs.zero initial data Ptrofs.zero 1 readonly called called_world).
  { eapply gateway_pending_run_ready with(source:=Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data Ptrofs.zero;Vlong Int64.one;Vint Int.zero]Kstop before);
      [apply gateway_read_context_ambient with(io:=io)(thread_errno:=thread_errno);exact thread|exact READY|exact PENDING|exact PREFIX]. }
  destruct(gateway_eof_receive_operation _ _ _ _ _ held called called_world(stream_descriptor initial)data Ptrofs.zero
    (Vlong Int64.zero)changed changed_world observed(proj1 CALLED)(proj1(proj2(proj2 CALLED)))
    (receive_context_pointer native stable discipline stream Ptrofs.zero initial data Ptrofs.zero 1 readonly
      None called called_world 1 CALLED ltac:(lia))OPERATION)
    as(count&bytes&COUNT&VALUE&LENGTH&LOAD&IO&REST).
  assert(ZERO:count=0).
  { assert(CASES:count=(-1)\/count=0\/count=1)by lia.
    destruct CASES as[SAME|[SAME|SAME]];subst count;try reflexivity;discriminate. }
  subst count;assert(EMPTY:bytes=[]).
  { apply length_zero_iff_nil;lia. }
  subst bytes;exists observed;split;[rewrite EVENTS;apply in_or_app;right;left;reflexivity|exact IO].
Qed.
