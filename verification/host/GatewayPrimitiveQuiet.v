(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: One actual SDK effect with no byte operation has no hidden IPC. *)
From Stdlib Require Import List.
From compcert Require Import Integers AST Values Memory Events Clight.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewayOperations GatewayReadonly GatewayPrimitiveCalls GatewaySendRuntime.
Import ListNotations.

Theorem gateway_external_no_io_projection {World Event}(backend:gateway_backend World Event)ge io
    events returned after next prefix suffix changed changed_world observed descriptor:
  events=prefix++gateway_primitive observed::suffix->Forall gateway_pending_event prefix->io observed=None->
  gateway_steps backend ge(gateway_live(Returnstate returned Kstop changed)changed_world)suffix
    (gateway_live(Returnstate returned Kstop after)next)->
  gateway_received_bytes io descriptor events=[] /\gateway_sent_bytes io descriptor events=[].
Proof.
  intros EVENTS PENDING IO SUFFIX.
  assert(QUIET:Forall gateway_quiet_event suffix).
  { eapply Forall_impl;[|eapply gateway_terminal_return_ambient;exact SUFFIX].
    intros event SAME;right;exact SAME. }
  split.
  - rewrite(gateway_external_received_projection backend ge io events returned after next prefix suffix changed changed_world observed
      descriptor EVENTS PENDING SUFFIX);cbn[gateway_received_event];rewrite IO;reflexivity.
  - rewrite EVENTS,gateway_sent_bytes_append,(gateway_pending_sent_empty io descriptor prefix PENDING).
    change(gateway_sent_event io descriptor(gateway_primitive observed)++gateway_sent_bytes io descriptor suffix=[]).
    cbn[gateway_sent_event];rewrite IO,(gateway_quiet_sent_empty io descriptor suffix QUIET);reflexivity.
Qed.
