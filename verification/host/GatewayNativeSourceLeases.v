(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The source-selected pending spawn binds its four already produced IPC leases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewaySpawnABI GatewaySpawnResources
  GatewaySDKInputs GatewayPairContext GatewayConnectionResources GatewayExchangeScope GatewaySpawnParentContext
  GatewayNativeImport GatewayNativeRows GatewayNativeReferences GatewayNativeSourceBinding.
Import ListNotations.
Local Close Scope lean_scope.
Module ND := GatewayNativeImport.

Theorem gateway_sdk_parent_leases {World} native stable discipline resources ipc readonly selected
    reference owner owned data_identity control_identity data control data_left data_right control_left control_right
    builders genuine actions attributes memory (world : World) :
  gateway_sdk_context native stable discipline resources ipc readonly selected reference owner owned
    data_identity control_identity data control data_left data_right control_left control_right
    builders genuine actions attributes memory world ->
  Forall (fun lease => gateway_owned_descriptor (resources world) (fst lease) (snd lease))
    (gateway_parent_ipc_leases ipc data_identity control_identity data_left data_right control_left control_right).
Proof.
  intros [[SIDE [FAMILY [VALID [DATA [CONTROL REST]]]]] OTHERS].
  unfold gateway_parent_ipc_leases; constructor.
  - exact (gateway_pair_lease_left _ _ _ _ _ DATA).
  - constructor; [exact (gateway_pair_lease_right _ _ _ _ _ DATA) |].
    constructor; [exact (gateway_pair_lease_left _ _ _ _ _ CONTROL) |].
    constructor; [exact (gateway_pair_lease_right _ _ _ _ _ CONTROL) |constructor].
Qed.

Theorem gateway_actual_spawn_row_leases {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view rows resources
    (runtime : gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    (representation : gateway_native_reference_runtime backend resources rows)
    native stable discipline ipc readonly selected reference owner owned data_identity control_identity data control
    data_left data_right control_left control_right actions attributes
    key initial_memory initial_world events memory world code arguments result after next observed :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world events memory world arguments code ->
  gateway_sdk_context native stable discipline resources ipc readonly selected reference owner owned
    data_identity control_identity data control data_left data_right control_left control_right
    builders genuine actions attributes memory world ->
  gateway_runtime_operation backend (gateway_spawn_signature gateway_posix_spawn_api) arguments
    memory world result after next observed ->
  exists selected_row row,
    rows world observed = Some (selected_row, row) /\
    gateway_native_row_process row = Nat_of_nat (gateway_source_process key) /\
    gateway_native_row_operation row = code /\
    (gateway_source_entry_position key <= selected_row)%nat /\
    Nat_of_nat (Pos.to_nat (gateway_source_actions key)) <>
      Nat_of_nat (Pos.to_nat (gateway_source_attributes key)) /\
    Forall (fun lease => gateway_native_lease_at (gateway_native_row_input row) (fst lease) (snd lease))
      (gateway_parent_ipc_leases ipc data_identity control_identity data_left data_right control_left control_right).
Proof.
  intros PENDING CONTEXT OPERATION.
  destruct (gateway_actual_spawn_row backend process position builders genuine actions_view attributes_view rows runtime
    key initial_memory initial_world events memory world code arguments result after next observed PENDING OPERATION)
    as [selected_row [row [ROW [PROCESS [INPUT [ORDER HEADERS]]]]]].
  exists selected_row, row; split; [exact ROW |]. split; [exact PROCESS |]. split; [exact INPUT |].
  split; [exact ORDER |]. split; [exact HEADERS |].
  eapply gateway_actual_row_leases; [exact representation |exact OPERATION |exact ROW |].
  eapply gateway_sdk_parent_leases; exact CONTEXT.
Qed.
