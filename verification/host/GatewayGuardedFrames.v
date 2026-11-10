(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Source control and individual runtime origins compose guarded global retention. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayGlobalAddresses GatewayPointerControl GatewayLinkedSource
  GatewayRuntimeMemory GatewayRuntimeCoverage GatewayCoveredPointers GatewaySourceCallbacks GatewayScopedBackend
  GatewayNoStoreControl GatewayOrdinaryMemory GatewaySourceFrames GatewayFrames.
Import ListNotations.

Definition gateway_source_frame_control {World Event} (backend : gateway_backend World Event) ge storage callback
    (source : gateway_state World) : Prop :=
  gateway_ordinary_state source \/ gateway_nostore_state (gateway_scoped_backend backend ge storage callback) ge source.

Lemma gateway_memory_origin_pointer private guard callback :
  gateway_callback_memory_origin private guard callback -> gateway_callback_pointer_origin private callback.
Proof.
  intros CALLBACK before arguments after result MEMORY LIVE ARGUMENTS RUN.
  destruct (CALLBACK before arguments after result MEMORY LIVE ARGUMENTS RUN) as [NEXT [RETAINED [RESULT FRAME]]].
  split; [exact NEXT |split; assumption].
Qed.

Theorem gateway_source_frame_control_step {World Event} (backend : gateway_backend World Event)
    runtime storage callback first observed target :
  gateway_runtime_registration runtime ->
  gateway_source_frame_control backend (Clight.globalenv (gateway_linked_program runtime)) storage callback first ->
  gateway_step (gateway_scoped_backend backend (Clight.globalenv (gateway_linked_program runtime)) storage callback)
    (Clight.globalenv (gateway_linked_program runtime)) first observed target ->
  gateway_source_frame_control backend (Clight.globalenv (gateway_linked_program runtime)) storage callback target.
Proof.
  intros REGISTERED [ORDINARY |NOSTORE] STEP.
  - left; eapply gateway_ordinary_step; eassumption.
  - right; eapply gateway_nostore_step; eassumption.
Qed.

Theorem gateway_source_control_frame {World Event} (backend : gateway_backend World Event)
    ge storage callback (guard : mem -> Prop) first observed target :
  (forall object, storage object -> ~ gateway_private_cell ge object) ->
  gateway_callback_memory_origin (gateway_private_cell ge) guard callback ->
  (forall before after, Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
    guard before -> guard after) ->
  gateway_pointer_state ge first -> gateway_source_frame_control backend ge storage callback first ->
  guard (gateway_state_memory first) ->
  gateway_step (gateway_scoped_backend backend ge storage callback) ge first observed target ->
  Mem.unchanged_on (fun object _ => gateway_private_cell ge object)
    (gateway_state_memory first) (gateway_state_memory target).
Proof.
  intros STORAGE CALLBACK RETAINS POINTER CONTROL ACTIVE STEP.
  inversion STEP; subst; cbn [gateway_state_memory] in ACTIVE |- *.
  - destruct CONTROL as [ORDINARY |NOSTORE].
    + eapply gateway_ordinary_internal_frame; eassumption.
    + eapply gateway_no_assignment_internal_frame; [exact H |exact POINTER | |exact H0].
      exact (gateway_nostore_current _ _ _ _ NOSTORE).
  - destruct H as [ORIGINAL EPISODE]; eapply gateway_scoped_episode_frame; eassumption.
  - destruct H0 as [ORIGINAL EPISODE]; eapply gateway_scoped_episode_frame; eassumption.
  - destruct H as [ORIGINAL EPISODE]; rewrite gateway_replace_memory_of.
    eapply gateway_scoped_episode_frame; eassumption.
  - apply Mem.unchanged_on_refl.
  - apply Mem.unchanged_on_refl.
  - destruct H as [ORIGINAL EPISODE]; eapply gateway_scoped_episode_frame; eassumption.
  - destruct H0 as [ORIGINAL EPISODE]; eapply gateway_scoped_episode_frame; eassumption.
Qed.

Theorem gateway_control_covered_prefix_frame {World Event} (backend : gateway_backend World Event)
    runtime storage callback (guard : mem -> Prop) first observed target :
  gateway_runtime_registration runtime ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  gateway_callback_memory_origin (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime))) guard callback ->
  (forall before after,
    Mem.unchanged_on (fun object _ => gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) before after ->
    guard before -> guard after) ->
  gateway_pointer_state (Clight.globalenv (gateway_linked_program runtime)) first ->
  gateway_source_frame_control backend (Clight.globalenv (gateway_linked_program runtime)) storage callback first ->
  guard (gateway_state_memory first) ->
  gateway_covered_steps backend (Clight.globalenv (gateway_linked_program runtime)) storage callback first observed target ->
  Mem.unchanged_on (fun object _ => gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object)
    (gateway_state_memory first) (gateway_state_memory target).
Proof.
  intros REGISTERED STORAGE CALLBACK RETAINS POINTER CONTROL ACTIVE RUN.
  revert POINTER CONTROL ACTIVE; induction RUN; intros POINTER CONTROL ACTIVE; [apply Mem.unchanged_on_refl |].
  pose proof (gateway_covered_scoped_step backend _ storage callback _ _ _ POINTER H) as SCOPED.
  pose proof (gateway_source_control_frame backend _ storage callback guard _ _ _
    STORAGE CALLBACK RETAINS POINTER CONTROL ACTIVE SCOPED) as FRAME.
  eapply Mem.unchanged_on_trans; [exact FRAME |].
  apply IHRUN.
  - eapply gateway_covered_pointer_step; [exact (proj1 REGISTERED) |exact STORAGE |
      eapply gateway_memory_origin_pointer; exact CALLBACK |exact POINTER |exact H].
  - eapply gateway_source_frame_control_step; eassumption.
  - eapply RETAINS; eassumption.
Qed.
