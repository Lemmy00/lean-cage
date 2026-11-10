(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Type checks retain the actual native iterator cells, including aliases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayOutcomeValidationContext
  GatewayThreadRuntime GatewayStreamInterface GatewayObjectDiscipline GatewayLocalRuntime GatewayFramedRuntime.

Definition gateway_validation_slot_region (environment : env) (object : block) (_ : Z) : Prop :=
  exists identifier ty, environment ! identifier = Some (object, ty).

Definition gateway_validation_slot_snapshot {World} environment saved memory (_ : World) : Prop :=
  Mem.unchanged_on (gateway_validation_slot_region environment) saved memory.

Lemma gateway_validation_slots_observer {World} python objects decimal_float ledger held reserved captured original protected source environment saved
    before world after next :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_validation_slot_snapshot environment saved before world ->
  gateway_observer_return (python world) (objects world) before (python next) (objects next) after ->
  gateway_validation_slot_snapshot environment saved after next.
Proof.
  intros CONTEXT SNAPSHOT OBSERVER; eapply Mem.unchanged_on_trans; [exact SNAPSHOT |].
  eapply Mem.unchanged_on_implies; [exact (gateway_observer_native _ _ _ _ _ _ OBSERVER) |].
  intros object position [identifier [ty LOOK]] LIVE.
  exact (proj2 (gateway_validation_environment _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT identifier object ty LOOK)).
Qed.

Lemma gateway_validation_slots_ambient {World Event} (backend : gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno
    (runtime : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    ledger held reserved captured original protected source environment saved before world after next :
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_validation_slot_snapshot environment saved before world ->
  gateway_interference backend before world after next -> gateway_validation_slot_snapshot environment saved after next.
Proof.
  intros CONTEXT SNAPSHOT AMBIENT.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next
    (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) AMBIENT) as [READY [ACCESS FRAME]].
  eapply Mem.unchanged_on_trans; [exact SNAPSHOT |].
  eapply Mem.unchanged_on_implies; [exact FRAME |].
  intros object position [identifier [ty LOOK]] LIVE; split; [left |cbn; tauto].
  exact (proj2 (gateway_validation_environment _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT identifier object ty LOOK)).
Qed.

Theorem gateway_validation_saved_slot {World} python objects decimal_float ledger held reserved captured original protected source environment
    before world after (next : World) identifier object ty chunk offset value :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_validation_slot_snapshot environment before after next ->
  environment ! identifier = Some (object, ty) -> Mem.load chunk before object offset = Some value ->
  Mem.load chunk after object offset = Some value.
Proof.
  intros CONTEXT SNAPSHOT LOOK LOAD.
  erewrite Mem.load_unchanged_on_1; [exact LOAD |exact SNAPSHOT | |].
  - exact (proj1 (gateway_validation_environment _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT identifier object ty LOOK)).
  - intros; exists identifier, ty; exact LOOK.
Qed.
