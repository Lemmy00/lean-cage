(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Only the actual committed send contributes outgoing bytes. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayReadonly GatewayPrimitiveCalls
  GatewaySendRuntime GatewayStreamInterface.
Import ListNotations.

Theorem gateway_external_sent_projection {World Event}(backend:gateway_backend World Event)ge io
    events returned after next prefix suffix changed changed_world observed descriptor:
  events=prefix++gateway_primitive observed::suffix->Forall gateway_pending_event prefix->
  gateway_steps backend ge(gateway_live(Returnstate returned Kstop changed)changed_world)suffix
    (gateway_live(Returnstate returned Kstop after)next)->
  gateway_sent_bytes io descriptor events=gateway_sent_event io descriptor(gateway_primitive observed).
Proof.
  intros EVENTS PENDING SUFFIX;subst events.
  rewrite gateway_sent_bytes_append,(gateway_pending_sent_empty io descriptor prefix PENDING).
  assert(EMPTY:gateway_sent_bytes io descriptor suffix=[]).
  { apply gateway_quiet_sent_empty;eapply Forall_impl;
      [intros event SAME;right;exact SAME|eapply gateway_terminal_return_ambient;exact SUFFIX]. }
  change(gateway_sent_event io descriptor(gateway_primitive observed)++gateway_sent_bytes io descriptor suffix=
    gateway_sent_event io descriptor(gateway_primitive observed)).
  rewrite EMPTY,app_nil_r;reflexivity.
Qed.

Theorem gateway_actual_primitive_no_send {World Event}(backend:gateway_backend World Event)ge io descriptor
    external types result_type convention arguments
    (input:mem->World->Prop)(discipline:gateway_runtime_discipline backend input)
    (operation:forall before world result after next observed,
      input before world->gateway_external backend external types result_type convention arguments
        before world result after next observed->io observed=None)
    before world events returned after next:
  input before world->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->gateway_sent_bytes io descriptor events=[].
Proof.
  intros READY RUN.
  destruct(gateway_external_operation_of_run backend ge external types result_type convention arguments
    before world events returned after next RUN)
    as(prefix & suffix & called & called_world & changed & changed_world & observed &
      EVENTS & PENDING & PREFIX & OPERATION & SUFFIX).
  assert(INPUT:input called called_world).
  { eapply gateway_pending_run_ready with(source:=Callstate(External external types result_type convention)arguments Kstop before);
      [exact discipline|exact READY|exact PENDING|exact PREFIX]. }
  pose proof(operation called called_world returned changed changed_world observed INPUT OPERATION)as IO.
  rewrite(gateway_external_sent_projection backend ge io events returned after next prefix suffix
    changed changed_world observed descriptor EVENTS PENDING SUFFIX).
  unfold gateway_sent_event;rewrite IO;reflexivity.
Qed.
