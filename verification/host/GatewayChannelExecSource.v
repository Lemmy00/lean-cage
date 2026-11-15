(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The exact source-built pair leases
   and SDK plan determine channels of the same actual birth and exec. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayNativeImport GatewayNativeRows GatewayNativeReferences
  GatewayNativeSourceBinding GatewayNativeSpawnSnapshots GatewayPendingNativeRows GatewaySpawnParentContext
  GatewayNativeFullTables GatewayNativeChannels GatewaySpawnDescriptors GatewaySpawnResources GatewaySpawnProcess
  GatewaySDKInputs GatewayPairContext GatewayExchangeSDK GatewayNativeStreamObservation.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Record gateway_native_channels_checked references data control : Prop := {
  gateway_native_channels_proof : ND.LeanCage_Host_NativeChannels_Evidence references data control
}.

Theorem gateway_actual_source_pair_exec_channels {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view resources rows births executed samples pending executing
    (actors : gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    (primitive : gateway_pending_spawn_runtime process position builders genuine actions_view attributes_view resources pending)
    (snapshots : gateway_native_spawn_snapshot_runtime builders genuine actions_view attributes_view
      births executed samples pending executing)
    native stable discipline ipc readonly protected reference owner owned
    (data_identity control_identity : gateway_pair_identity ipc) data control
    data_left data_right control_left control_right
    key initial_memory initial_world source_events memory world arguments code
    born birth_position birth_row child current selected row image :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world source_events memory world arguments code ->
  gateway_sdk_context native stable discipline resources ipc readonly protected reference owner owned
    data_identity control_identity data control data_left data_right control_left control_right builders genuine
    (Some (Vptr (gateway_source_actions key) Ptrofs.zero, exchange_sdk_plan data_right control_right))
    (Some (Vptr (gateway_source_attributes key) Ptrofs.zero, exchange_sdk_attributes)) memory world ->
  4 <= data_right -> 4 <= control_right -> pair_right_object ipc data_identity <> pair_right_object ipc control_identity ->
  pending arguments memory world born birth_position birth_row -> samples born birth_position = Some birth_row ->
  gateway_native_row_product birth_row = ND.LeanCage_Host_NativeCode_Product_created (Nat_of_nat child) ->
  executing arguments memory world child current selected row -> samples current selected = Some row ->
  gateway_native_row_process row = Nat_of_nat child ->
  gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_executed (Nat_of_nat image) ->
  exists birth execution,
    births born child = Some birth /\ births current child = Some birth /\ executed current child execution /\
    gateway_exec_from_birth birth execution /\ gateway_exec_image_object execution = image /\
    gateway_native_row_operation row = gateway_native_execution_code execution /\
    gateway_native_full_table_view (gateway_exec_descriptors execution) (gateway_native_row_output row) /\
    gateway_native_channels_checked (gateway_native_row_output row)
      (Nat_of_nat (pair_right_object ipc data_identity)) (Nat_of_nat (pair_right_object ipc control_identity)).
Proof.
  intros SOURCE CONTEXT DATA_BOUND CONTROL_BOUND SEPARATE PENDING BIRTH_ROW CREATED EXECUTING ROW PROCESS IMAGE.
  destruct (gateway_actual_pending_spawn_row_leases backend process position builders genuine actions_view attributes_view rows
    resources pending actors primitive native stable discipline ipc readonly protected reference owner owned data_identity control_identity
    data control data_left data_right control_left control_right
    (Some (Vptr (gateway_source_actions key) Ptrofs.zero, exchange_sdk_plan data_right control_right))
    (Some (Vptr (gateway_source_attributes key) Ptrofs.zero, exchange_sdk_attributes))
    key initial_memory initial_world source_events memory world arguments code born birth_position birth_row
    SOURCE CONTEXT PENDING) as (ACTOR & INPUT & ORDER & HEADERS & LEASES).
  destruct (gateway_actual_source_exec_snapshot backend process position builders genuine actions_view attributes_view births executed
    samples pending executing snapshots key initial_memory initial_world source_events memory world arguments code
    born birth_position birth_row child current selected row image (exchange_sdk_plan data_right control_right)
    SOURCE (proj1 (proj2 (proj2 CONTEXT))) PENDING BIRTH_ROW CREATED EXECUTING ROW PROCESS IMAGE)
    as (birth & execution & SAME_SOURCE & BIRTH & RETAINED & EXECUTED & CAPTURE & PLAN & INHERITED & EXEC & IDENTITY & CODE & FULL).
  assert (DATA_LEASE : gateway_native_lease_at (gateway_native_row_input birth_row) data_right (pair_right_entry ipc data_identity)).
  { inversion LEASES as [|first rest FIRST TAIL]; subst.
    inversion TAIL as [|second remaining SECOND REST]; subst; exact SECOND. }
  assert (CONTROL_LEASE : gateway_native_lease_at (gateway_native_row_input birth_row) control_right
    (pair_right_entry ipc control_identity)).
  { inversion LEASES as [|first rest FIRST TAIL]; subst.
    inversion TAIL as [|second remaining SECOND REST]; subst.
    inversion REST as [|third remaining' THIRD REST']; subst.
    inversion REST' as [|fourth remaining'' FOURTH EMPTY]; subst; exact FOURTH. }
  exists birth, execution.
  split; [exact BIRTH |]. split; [exact RETAINED |]. split; [exact EXECUTED |]. split; [exact EXEC |].
  split; [exact IDENTITY |]. split; [exact CODE |]. split; [exact FULL |].
  constructor; eapply gateway_native_execution_channel_evidence with
    (birth := birth) (execution := execution) (data_fd := data_right) (control_fd := control_right)
    (data := pair_right_entry ipc data_identity) (control := pair_right_entry ipc control_identity).
  - exact EXEC.
  - exact PLAN.
  - exact DATA_BOUND.
  - exact CONTROL_BOUND.
  - eapply gateway_native_full_table_source_lease; eassumption.
  - eapply gateway_native_full_table_source_lease; eassumption.
  - exact SEPARATE.
  - exact (proj1 FULL).
Qed.
