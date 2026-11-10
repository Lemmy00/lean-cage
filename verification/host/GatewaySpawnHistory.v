(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual selected exec retains the same earlier native spawn birth. *)
From Stdlib Require Import List ZArith.
From compcert Require Import AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewaySpawnABI GatewaySpawnResources
  GatewaySpawnActions GatewaySpawnProcess GatewaySpawnDescriptors GatewaySpawnImport GatewaySpawnProjection GatewaySpawnHandoff.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_state_world {World} (state : gateway_state World) : World :=
  match state with gateway_live _ world | gateway_dead _ world => world end.

Lemma gateway_child_history_identity history : gateway_child_history_retained history history.
Proof. intros token birth LIVE; exact LIVE. Qed.
Lemma gateway_child_history_transitive first middle last :
  gateway_child_history_retained first middle -> gateway_child_history_retained middle last ->
  gateway_child_history_retained first last.
Proof. intros LEFT RIGHT token birth LIVE; apply RIGHT, LEFT; exact LIVE. Qed.

Section BirthHistory.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline resources builders genuine footprint
  births executed (runtime : gateway_spawn_process_runtime backend io native stable discipline resources builders genuine
    footprint births executed).

Theorem gateway_native_step_retains_birth ge before event after :
  gateway_step backend ge before event after ->
  gateway_child_history_retained (births (gateway_state_world before)) (births (gateway_state_world after)).
Proof.
  intro STEP; inversion STEP; subst; cbn;
    try apply gateway_child_history_identity.
  - eapply (gateway_birth_passive backend io native stable discipline resources builders genuine footprint births executed runtime)
      with (definition := External ef types result_type convention); cbn; eassumption.
  - eapply (gateway_birth_builtin backend io native stable discipline resources builders genuine footprint births executed runtime); eassumption.
  - eapply (gateway_birth_ambient backend io native stable discipline resources builders genuine footprint births executed runtime); eassumption.
  - eapply (gateway_birth_passive backend io native stable discipline resources builders genuine footprint births executed runtime)
      with (definition := External ef types result_type convention); cbn; eassumption.
  - eapply (gateway_birth_builtin backend io native stable discipline resources builders genuine footprint births executed runtime); eassumption.
Qed.

Theorem gateway_native_prefix_retains_birth ge before events after :
  gateway_steps backend ge before events after ->
  gateway_child_history_retained (births (gateway_state_world before)) (births (gateway_state_world after)).
Proof.
  intro RUN; induction RUN; [apply gateway_child_history_identity |].
  eapply gateway_child_history_transitive; [eapply gateway_native_step_retains_birth; exact H |exact IHRUN].
Qed.

Theorem gateway_same_spawn_exec ge before spawned path arguments environment actions attributes
    (receipt : gateway_spawn_birth_receipt resources births before spawned path arguments environment actions attributes)
    source events final execution :
  gateway_steps backend ge (gateway_live source spawned) events final ->
  executed (gateway_state_world final) (gateway_spawned_token _ _ _ _ _ _ _ _ _ receipt) execution ->
  gateway_exec_from_birth (gateway_spawned_birth _ _ _ _ _ _ _ _ _ receipt) execution.
Proof.
  intros RUN EXECUTED.
  destruct (gateway_execution_origin backend io native stable discipline resources builders genuine footprint births executed runtime _ _ _ EXECUTED)
    as [birth [OBSERVED EXEC]].
  pose proof (gateway_native_prefix_retains_birth _ _ _ _ RUN) as RETAINED.
  specialize (RETAINED _ _ (gateway_spawned_recorded _ _ _ _ _ _ _ _ _ receipt)); cbn in RETAINED.
  rewrite OBSERVED in RETAINED; inversion RETAINED; subst birth; exact EXEC.
Qed.

Theorem gateway_actual_spawn_exec_channels ge before spawned path arguments environment data_fd control_fd attributes
    (receipt : gateway_spawn_birth_receipt resources births before spawned path arguments environment
      (gateway_private_spawn_plan data_fd control_fd) attributes)
    source events final execution data control :
  gateway_steps backend ge (gateway_live source spawned) events final ->
  executed (gateway_state_world final) (gateway_spawned_token _ _ _ _ _ _ _ _ _ receipt) execution ->
  4 <= data_fd -> 4 <= control_fd ->
  gateway_owned_descriptor (resources before) data_fd data ->
  gateway_owned_descriptor (resources before) control_fd control ->
  gateway_resource_object (gateway_descriptor_object data) <>
    gateway_resource_object (gateway_descriptor_object control) ->
  LeanCage_Host_NativeSpawn_ChannelEvidence (gateway_shared_descriptors (gateway_exec_descriptors execution))
    (gateway_shared_descriptor (gateway_inherited_endpoint data))
    (gateway_shared_descriptor (gateway_inherited_endpoint control)).
Proof.
  intros RUN EXEC DATA_BOUND CONTROL_BOUND DATA CONTROL SEPARATE.
  eapply (gateway_spawned_execution_channels resources births before spawned path arguments environment
    data_fd control_fd attributes receipt execution data control); try eassumption.
  eapply gateway_same_spawn_exec; eassumption.
Qed.
End BirthHistory.
