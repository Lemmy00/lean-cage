(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Pointer and control scopes derive each actual source memory frame. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayPointerControl GatewayPointerEntry GatewayLinkedSource
  GatewayOrdinarySource GatewayOrdinaryControl GatewayOrdinaryExecution GatewayOrdinaryMemory GatewayScopedMemory
  GatewayNoStoreControl.
Import ListNotations.

Theorem gateway_no_assignment_internal_frame ge source observed target :
  internal_state source -> gateway_pointer_source ge source -> gateway_not_assignment source ->
  step2 ge source observed target ->
  Mem.unchanged_on (gateway_private_cells_region ge) (memory_of source) (memory_of target).
Proof.
  intros INTERNAL POINTER NOASSIGN STEP.
  inversion STEP; subst; cbn [internal_state] in INTERNAL; try contradiction;
    cbn [memory_of]; try apply Mem.unchanged_on_refl.
  - destruct POINTER as [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]].
    eapply gateway_environment_avoids_free; [|eassumption].
    intros identifier object ty position LOOKUP; exact (LOCALS identifier object ty LOOKUP).
  - destruct POINTER as [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]].
    eapply gateway_environment_avoids_free; [|eassumption].
    intros identifier object ty position LOOKUP; exact (LOCALS identifier object ty LOOKUP).
  - destruct POINTER as [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]].
    eapply gateway_environment_avoids_free; [|eassumption].
    intros identifier object ty position LOOKUP; exact (LOCALS identifier object ty LOOKUP).
  - destruct POINTER as [MEMORY [LIVE CONTROL]]; inversion H; subst.
    match goal with ALLOC : alloc_variables _ _ _ _ _ _ |- _ =>
      destruct (gateway_scope_allocation ge (gateway_private_cells_region ge) _ _ _ _ _ ALLOC
        (fun object position PRIVATE => LIVE object PRIVATE) (gateway_environment_empty_avoids _)) as [ENVIRONMENT FRAME]
    end.
    exact FRAME.
Qed.

Lemma gateway_ordinary_memory_replace source after :
  gateway_ordinary_source source -> gateway_ordinary_source (gateway_replace_memory source after).
Proof. destruct source; exact (fun x => x). Qed.

Definition gateway_ordinary_state {World} (source : gateway_state World) : Prop :=
  match source with gateway_live source _ => gateway_ordinary_source source |gateway_dead _ _ => True end.

Theorem gateway_ordinary_step {World Event} (backend : gateway_backend World Event) runtime first observed target :
  gateway_runtime_registration runtime -> gateway_ordinary_state first ->
  gateway_step backend (Clight.globalenv (gateway_linked_program runtime)) first observed target ->
  gateway_ordinary_state target.
Proof.
  intros REGISTERED READY STEP; inversion STEP; subst; cbn [gateway_ordinary_state] in READY |- *; try exact I.
  - eapply gateway_ordinary_internal_source; eassumption.
  - exact (proj2 READY).
  - destruct READY as [WHOLE [CURRENT [CONTINUATION GLOBALS]]].
    repeat split; assumption || reflexivity.
  - apply gateway_ordinary_memory_replace; exact READY.
  - exact READY.
Qed.

Theorem gateway_ordinary_prefix {World Event} (backend : gateway_backend World Event) runtime first observed target :
  gateway_runtime_registration runtime -> gateway_ordinary_state first ->
  gateway_steps backend (Clight.globalenv (gateway_linked_program runtime)) first observed target ->
  gateway_ordinary_state target.
Proof.
  intros REGISTERED READY RUN; revert READY; induction RUN; intro READY; [exact READY |].
  apply IHRUN; eapply gateway_ordinary_step; eassumption.
Qed.
