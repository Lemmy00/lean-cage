(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Child channel facts follow from the same actual birth and exec. *)
From Stdlib Require Import ZArith List.
From HostGateway Require Import GatewaySpawnDescriptors GatewaySpawnResources GatewaySpawnActions
  GatewaySpawnProcess GatewaySpawnImport GatewaySpawnProjection.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_inherited_endpoint (entry : gateway_resource_descriptor) : gateway_resource_descriptor :=
  {| gateway_descriptor_object := gateway_descriptor_object entry; gateway_descriptor_cloexec := false |}.

Theorem gateway_recorded_execution_channels birth execution data_fd control_fd data control :
  gateway_exec_from_birth birth execution ->
  gateway_child_actions birth = gateway_private_spawn_plan data_fd control_fd ->
  4 <= data_fd -> 4 <= control_fd ->
  gateway_child_inherited birth data_fd = Some data -> gateway_child_inherited birth control_fd = Some control ->
  gateway_resource_object (gateway_descriptor_object data) <>
    gateway_resource_object (gateway_descriptor_object control) ->
  LeanCage_Host_NativeSpawn_ChannelEvidence
    (gateway_shared_descriptors (gateway_exec_descriptors execution))
    (gateway_shared_descriptor (gateway_inherited_endpoint data))
    (gateway_shared_descriptor (gateway_inherited_endpoint control)).
Proof.
  intros [_ [_ [_ [prepared [APPLIED EXEC]]]]] PLAN DATA_BOUND CONTROL_BOUND DATA CONTROL SEPARATE.
  rewrite PLAN in APPLIED.
  destruct (gateway_private_spawn_descriptors _ _ _ _ _ DATA_BOUND CONTROL_BOUND DATA CONTROL)
    as [expected [SAME [INPUT [OUTPUT [CANCELLATION CLOSED]]]]].
  rewrite APPLIED in SAME; inversion SAME; subst expected.
  rewrite EXEC.
  eapply gateway_shared_channel_evidence; try eassumption; reflexivity.
Qed.

Theorem gateway_spawned_execution_channels {World} (resources : World -> gateway_resource_state)
    (births : World -> nat -> option gateway_child_birth) before spawned path arguments environment
    data_fd control_fd attributes (receipt : gateway_spawn_birth_receipt resources births before spawned
      path arguments environment (gateway_private_spawn_plan data_fd control_fd) attributes)
    execution data control :
  gateway_exec_from_birth (gateway_spawned_birth _ _ _ _ _ _ _ _ _ receipt) execution ->
  4 <= data_fd -> 4 <= control_fd ->
  gateway_owned_descriptor (resources before) data_fd data ->
  gateway_owned_descriptor (resources before) control_fd control ->
  gateway_resource_object (gateway_descriptor_object data) <>
    gateway_resource_object (gateway_descriptor_object control) ->
  LeanCage_Host_NativeSpawn_ChannelEvidence
    (gateway_shared_descriptors (gateway_exec_descriptors execution))
    (gateway_shared_descriptor (gateway_inherited_endpoint data))
    (gateway_shared_descriptor (gateway_inherited_endpoint control)).
Proof.
  intros EXEC DATA_BOUND CONTROL_BOUND DATA CONTROL SEPARATE.
  eapply gateway_recorded_execution_channels with (data_fd := data_fd) (control_fd := control_fd); try eassumption.
  - exact (gateway_spawned_actions _ _ _ _ _ _ _ _ _ receipt).
  - apply (gateway_spawned_inherited _ _ _ _ _ _ _ _ _ receipt); exact DATA.
  - apply (gateway_spawned_inherited _ _ _ _ _ _ _ _ _ receipt); exact CONTROL.
Qed.
