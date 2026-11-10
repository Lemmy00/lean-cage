(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Non-I/O primitive occurrences retain exact waiting
   traces. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayOperations GatewayFramedRuntime GatewayPrimitiveCalls
  GatewayStreamInterface GatewaySendRuntime GatewayErrnoFragment.
Import ListNotations.

Theorem gateway_actual_primitive_silent {World Event}(backend:gateway_backend World Event)ge io
    external types result_type convention arguments property(CLOSED:gateway_ambient_closed backend property)
    (OPERATION:forall memory current result changed future observed,property memory current->
      gateway_external backend external types result_type convention arguments memory current result changed future observed->
      io observed=None)
    before world events returned after next:
  property before world->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->gateway_errno_silent io events.
Proof.
  intros READY RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as(prefix&suffix&called&called_world&changed&changed_world&observed&EVENTS&PENDING&PREFIX&API&SUFFIX).
  assert(CALLED:property called called_world).
  { eapply gateway_pending_run_ready with(source:=Callstate(External external types result_type convention)arguments Kstop before);
      [exact CLOSED|exact READY|exact PENDING|exact PREFIX]. }
  pose proof(OPERATION _ _ _ _ _ _ CALLED API)as EMPTY.
  rewrite EVENTS;apply gateway_errno_silent_append;[apply gateway_errno_silent_pending;exact PENDING|].
  apply gateway_errno_silent_append with(first:=[gateway_primitive observed]).
  - intros descriptor;split;unfold gateway_received_bytes,gateway_sent_bytes;
      cbn[flat_map gateway_received_event gateway_sent_event];rewrite EMPTY;reflexivity.
  - apply gateway_errno_silent_ambient;eapply gateway_terminal_return_ambient;exact SUFFIX.
Qed.
