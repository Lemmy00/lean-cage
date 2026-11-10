(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Both source interpreter queries retain facts from their individual effects. *)
From Stdlib Require Import List.
From compcert Require Import AST Integers Values Memory Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayInterpreterSource GatewayInterpreterRuntime GatewayRuntime GatewayOperations
  GatewayReadonly GatewayFramedRuntime GatewayStreamInterface.
Import ListNotations.

Definition gateway_interpreter_definition (get : bool) :=
  if get then gateway_interpreter_get_definition else gateway_interpreter_id_definition.
Definition gateway_interpreter_result {World} (current : World -> Values.val) (identifier : World -> int64)
    (get : bool) world result : Prop :=
  if get then result = current world /\ exists object offset, result = Vptr object offset
  else result = Vlong (identifier world).

Theorem gateway_interpreter_run_retained {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    io native stable base python objects current identifier
    (runtime : gateway_interpreter_runtime backend io native stable base python objects current identifier)
    (property : mem -> World -> Prop) (get : bool) arguments before world events result after next :
  gateway_ambient_closed backend property ->
  (forall memory owner, property memory owner -> base None memory owner /\
    arguments = if get then [] else [current owner]) ->
  (forall memory owner changed following observed, property memory owner ->
    gateway_interpreter_query_post io native stable base python objects current identifier memory owner changed following observed ->
    property changed following) ->
  property before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (gateway_interpreter_definition get) arguments Kstop before) world) events
    (gateway_live (Returnstate result Kstop after) next) ->
  property after next /\
  exists prefix suffix called called_world changed changed_world observed,
    events = prefix ++ gateway_primitive observed :: suffix /\
    property called called_world /\
    gateway_runtime_operation backend (gateway_interpreter_definition get) arguments
      called called_world result changed changed_world observed /\
    gateway_interpreter_result current identifier get called_world result /\
    gateway_interpreter_query_post io native stable base python objects current identifier
      called called_world changed changed_world observed.
Proof.
  intros CLOSED INPUTS EFFECT INPUT RUN.
  assert (SELECTED : exists prefix suffix called called_world changed changed_world observed,
    events = prefix ++ gateway_primitive observed :: suffix /\ Forall gateway_pending_event prefix /\
    gateway_steps backend ge
      (gateway_live (Callstate (gateway_interpreter_definition get) arguments Kstop before) world) prefix
      (gateway_live (Callstate (gateway_interpreter_definition get) arguments Kstop called) called_world) /\
    gateway_runtime_operation backend (gateway_interpreter_definition get) arguments called called_world result changed changed_world observed /\
    gateway_steps backend ge (gateway_live (Returnstate result Kstop changed) changed_world) suffix
      (gateway_live (Returnstate result Kstop after) next)).
  { destruct get; unfold gateway_interpreter_definition in *;
      eapply gateway_external_operation_of_run; exact RUN. }
  destruct SELECTED as (prefix & suffix & called & called_world & changed & changed_world & observed &
    EVENTS & PENDING & PREFIX & OPERATION & SUFFIX).
  pose proof (gateway_pending_run_ready backend ge property CLOSED
    (Callstate (gateway_interpreter_definition get) arguments Kstop before) before world prefix called called_world
    INPUT PENDING PREFIX) as CALLED.
  destruct (INPUTS called called_world CALLED) as [BASE ARGUMENTS].
  assert (RETURN : gateway_interpreter_result current identifier get called_world result /\
    gateway_interpreter_query_post io native stable base python objects current identifier called called_world changed changed_world observed).
  { destruct get; cbn [gateway_interpreter_result gateway_interpreter_definition] in *; subst arguments.
    - destruct (gateway_interpreter_get_operation _ _ _ _ _ _ _ _ _ runtime called called_world result changed changed_world observed BASE OPERATION)
        as [SAME [POINTER POST]]; exact (conj (conj SAME POINTER) POST).
    - eapply gateway_interpreter_id_operation; eassumption. }
  destruct RETURN as [VALUE POST].
  assert (CHANGED : property changed changed_world) by (eapply EFFECT; eassumption).
  assert (FINAL : property after next).
  { exact (gateway_readonly_run_side backend ge property CLOSED (Returnstate result Kstop changed)
      changed_world suffix result after next I CHANGED SUFFIX). }
  split; [exact FINAL |]. exists prefix, suffix, called, called_world, changed, changed_world, observed.
  split; [exact EVENTS |]. split; [exact CALLED |]. split; [exact OPERATION |]. split; assumption.
Qed.
