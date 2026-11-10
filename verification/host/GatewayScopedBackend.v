(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The exact observed SDK row retains its proved pointer inputs. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayGlobalAddresses GatewayPointerOrigins GatewayPointerMemory
  GatewayPointerControl GatewayLinkedSource GatewayRuntimeMemory GatewayRuntimeCoverage GatewayCoveredPointers.
Import ListNotations.

Definition gateway_scoped_episode ge storage callback before arguments after : Prop :=
  gateway_runtime_memory_scope (gateway_private_cell ge) before arguments /\
  exists pool, gateway_runtime_memory_steps ge storage callback before arguments after pool.

(* This is a view of the SAME primitive, not a replacement runtime. The source
   producer below supplies its input scopes from the actual predecessor state;
   both returned and committed-lost rows retain the original physical effect. *)
Definition gateway_scoped_backend {World Event} (backend : gateway_backend World Event) ge storage callback :
    gateway_backend World Event := {|
  gateway_external := fun ef types result_type convention arguments before world result after next observed =>
    gateway_external backend ef types result_type convention arguments before world result after next observed /\
    gateway_scoped_episode ge storage callback before arguments after;
  gateway_builtin := fun ef types arguments before world result after next observed =>
    gateway_builtin backend ef types arguments before world result after next observed /\
    gateway_scoped_episode ge storage callback before arguments after;
  gateway_interference := fun before world after next =>
    gateway_interference backend before world after next /\ gateway_scoped_episode ge storage callback before [] after
|}.

Theorem gateway_scoped_episode_frame ge storage callback (guard : mem -> Prop) before arguments after :
  (forall object, storage object -> ~ gateway_private_cell ge object) ->
  gateway_callback_memory_origin (gateway_private_cell ge) guard callback ->
  (forall before after, Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
    guard before -> guard after) ->
  gateway_scoped_episode ge storage callback before arguments after -> guard before ->
  Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after.
Proof.
  intros STORAGE CALLBACK RETAINS [READY [pool RUN]] ACTIVE.
  exact (proj2 (gateway_runtime_memory_steps_origin ge storage callback _ guard
    before arguments after pool STORAGE CALLBACK RETAINS READY RUN) ACTIVE).
Qed.

Theorem gateway_covered_scoped_step {World Event} (backend : gateway_backend World Event) ge storage callback
    first observed target :
  gateway_pointer_state ge first -> gateway_covered_step backend ge storage callback first observed target ->
  gateway_step (gateway_scoped_backend backend ge storage callback) ge first observed target.
Proof.
  intros READY STEP; inversion STEP; subst.
  - apply gateway_internal; assumption.
  - apply gateway_external_returned; split; [exact H |]. split.
    + exact (conj (proj1 READY) (conj (proj1 (proj2 READY)) (proj2 (proj2 (proj2 (proj2 READY)))))).
    + eexists; exact H0.
  - eapply gateway_builtin_returned; [exact H |]. split; [exact H0 |]. split.
    + split; [exact (proj1 READY) |split; [exact (proj1 (proj2 READY)) |]].
      eapply gateway_pointer_builtin_arguments; eassumption.
    + eexists; exact H1.
  - apply gateway_interleaved; split; [exact H |]. split.
    + split; [exact (proj1 READY) |split; [exact (proj1 (proj2 READY)) |constructor]].
    + eexists; exact H0.
  - apply gateway_waiting; exact H.
  - apply gateway_process_lost.
  - eapply gateway_external_committed_lost; split; [exact H |]. split.
    + exact (conj (proj1 READY) (conj (proj1 (proj2 READY)) (proj2 (proj2 (proj2 (proj2 READY)))))).
    + eexists; exact H0.
  - eapply gateway_builtin_committed_lost; [exact H |]. split; [exact H0 |]. split.
    + split; [exact (proj1 READY) |split; [exact (proj1 (proj2 READY)) |]].
      eapply gateway_pointer_builtin_arguments; eassumption.
    + eexists; exact H1.
Qed.

Theorem gateway_covered_scoped_prefix {World Event} (backend : gateway_backend World Event) runtime storage callback
    first observed target :
  forallb gateway_runtime_function runtime = true ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  gateway_callback_pointer_origin (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime))) callback ->
  gateway_pointer_state (Clight.globalenv (gateway_linked_program runtime)) first ->
  gateway_covered_steps backend (Clight.globalenv (gateway_linked_program runtime)) storage callback first observed target ->
  gateway_steps (gateway_scoped_backend backend (Clight.globalenv (gateway_linked_program runtime)) storage callback)
    (Clight.globalenv (gateway_linked_program runtime)) first observed target.
Proof.
  intros RUNTIME STORAGE CALLBACK READY RUN; revert READY; induction RUN; intro READY; [constructor |].
  econstructor; [eapply gateway_covered_scoped_step; [exact READY |exact H] |].
  apply IHRUN; eapply gateway_covered_pointer_step; eassumption.
Qed.
