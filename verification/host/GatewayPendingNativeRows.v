(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: An actual fork inside a pending SDK call needs no future SDK reply. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnHistory GatewayNativeImport
  GatewayNativeRows GatewayNativeReferences GatewayNativeSourceLeases GatewayNativeSourceBinding
  GatewayNativeSpawnOperands GatewaySpawnParentContext GatewaySDKInputs GatewaySpawnResources.
Import ListNotations.
Local Close Scope lean_scope.
Module ND := GatewayNativeImport.

(* The observer denotes the SAME physical native spawn row inside the SDK
   invocation begun with these entry arguments/memory/world. The last world
   merely contains that already observed row; no SDK result/return is required.
   The ordinary consumer identifies its actual global NativeCallAt position. *)
Record gateway_pending_spawn_runtime {World} (process position : World -> nat)
    builders genuine actions_view attributes_view (resources : World -> gateway_resource_state)
    (pending : list Values.val -> mem -> World -> World -> nat -> ND.LeanCage_Host_NativeCode_CallRow -> Prop) : Prop := {
  gateway_pending_spawn_primitive : forall arguments memory world current selected row code,
    gateway_native_spawn_operands builders genuine actions_view attributes_view memory world arguments code ->
    pending arguments memory world current selected row ->
    gateway_native_row_process row = Nat_of_nat (process world) /\
    gateway_native_row_operation row = code /\ (position world <= selected < position current)%nat /\
    gateway_native_leased_references (resources world) (gateway_native_row_input row)
}.

Theorem gateway_actual_pending_spawn_row {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view rows resources pending
    (actors : gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    (primitive : gateway_pending_spawn_runtime process position builders genuine actions_view attributes_view resources pending)
    key initial_memory initial_world events memory world arguments code current selected row :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world events memory world arguments code ->
  pending arguments memory world current selected row ->
  gateway_native_row_process row = Nat_of_nat (gateway_source_process key) /\
  gateway_native_row_operation row = code /\
  (gateway_source_entry_position key <= selected < position current)%nat /\
  Nat_of_nat (Pos.to_nat (gateway_source_actions key)) <>
    Nat_of_nat (Pos.to_nat (gateway_source_attributes key)) /\
  gateway_native_leased_references (resources world) (gateway_native_row_input row).
Proof.
  intros [SOURCE] OBSERVED.
  destruct SOURCE as (entry_arguments & environment & temporaries & allocated & blocks & symbols & continuation & ENTRY & ARGUMENTS & PREFIX &
    ACTIONS & ATTRIBUTES & FRESH_ACTIONS & FRESH_ATTRIBUTES & DISTINCT & PROCESS & POSITION & INPUTS).
  destruct (gateway_native_run_actor backend process position builders genuine actions_view attributes_view rows actors
    (Clight.globalenv prog) _ _ _ PREFIX) as [SAME_PROCESS LATER].
  cbn [gateway_state_world] in SAME_PROCESS, LATER.
  destruct (gateway_pending_spawn_primitive _ _ _ _ _ _ _ _ primitive arguments memory world current selected row code INPUTS OBSERVED)
    as [ACTOR [INPUT [ORDER LEASES]]].
  split; [rewrite ACTOR, PROCESS, SAME_PROCESS; reflexivity |]. split; [exact INPUT |].
  split; [lia |]. split; [|exact LEASES].
  intro SAME; apply (f_equal nat_of_Nat) in SAME; repeat rewrite nat2Natid in SAME.
  apply DISTINCT, Pos2Nat.inj; exact SAME.
Qed.

Theorem gateway_actual_pending_spawn_row_leases {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view rows resources pending
    (actors : gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    (primitive : gateway_pending_spawn_runtime process position builders genuine actions_view attributes_view resources pending)
    native stable discipline ipc readonly protected reference owner owned data_identity control_identity data control
    data_left data_right control_left control_right actions attributes
    key initial_memory initial_world events memory world arguments code current selected row :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world events memory world arguments code ->
  gateway_sdk_context native stable discipline resources ipc readonly protected reference owner owned
    data_identity control_identity data control data_left data_right control_left control_right
    builders genuine actions attributes memory world ->
  pending arguments memory world current selected row ->
  gateway_native_row_process row = Nat_of_nat (gateway_source_process key) /\
  gateway_native_row_operation row = code /\
  (gateway_source_entry_position key <= selected < position current)%nat /\
  Nat_of_nat (Pos.to_nat (gateway_source_actions key)) <>
    Nat_of_nat (Pos.to_nat (gateway_source_attributes key)) /\
  Forall (fun lease => gateway_native_lease_at (gateway_native_row_input row) (fst lease) (snd lease))
    (gateway_parent_ipc_leases ipc data_identity control_identity data_left data_right control_left control_right).
Proof.
  intros SOURCE CONTEXT OBSERVED.
  destruct (gateway_actual_pending_spawn_row backend process position builders genuine actions_view attributes_view rows resources pending
    actors primitive key initial_memory initial_world events memory world arguments code current selected row SOURCE OBSERVED)
    as [PROCESS [INPUT [ORDER [HEADERS LEASES]]]].
  split; [exact PROCESS |]. split; [exact INPUT |]. split; [exact ORDER |]. split; [exact HEADERS |].
  pose proof (gateway_sdk_parent_leases native stable discipline resources ipc readonly protected reference owner owned
    data_identity control_identity data control data_left data_right control_left control_right builders genuine actions attributes memory world CONTEXT)
    as OWNED.
  eapply Forall_impl; [|exact OWNED]. intros [descriptor entry] OWNERSHIP; cbn in *; apply LEASES; exact OWNERSHIP.
Qed.
