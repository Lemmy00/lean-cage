(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Bind source-owned operands and invocation identity to the same primitive row. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewaySpawnHistory GatewaySpawnABI
  GatewayNativeImport GatewayNativeCallOperands GatewayNativeSpawnOperands GatewayNativeSourceBinding.
Import ListNotations.
Local Close Scope lean_scope.
Local Opaque Nat_of_nat.
Module ND := GatewayNativeImport.

Definition gateway_native_row_process (row : ND.LeanCage_Host_NativeCode_CallRow) : Lean.Nat :=
  match row with ND.LeanCage_Host_NativeCode_CallRow_mk process _ _ _ _ _ _ => process end.
Definition gateway_native_row_operation (row : ND.LeanCage_Host_NativeCode_CallRow) :=
  match row with ND.LeanCage_Host_NativeCode_CallRow_mk _ _ _ _ operation _ _ => operation end.

Definition gateway_native_shared_key (key : gateway_native_source_key) :=
  ND.LeanCage_Host_NativeCode_SourceKey_mk
    (Nat_of_nat (gateway_source_process key)) (Nat_of_nat (gateway_source_entry_position key))
    (Nat_of_nat (Pos.to_nat (gateway_source_actions key)))
    (Nat_of_nat (Pos.to_nat (gateway_source_attributes key))).

Inductive gateway_native_operation_inputs {World} builders genuine actions_view attributes_view
    memory (world : World) definition values code : Prop :=
| gateway_native_direct_inputs : gateway_native_call_operands memory definition values code ->
    gateway_native_operation_inputs builders genuine actions_view attributes_view memory world definition values code
| gateway_native_spawn_inputs : definition = gateway_spawn_signature gateway_posix_spawn_api ->
    gateway_native_spawn_operands builders genuine actions_view attributes_view memory world values code ->
    gateway_native_operation_inputs builders genuine actions_view attributes_view memory world definition values code.

(* This is a single-operation ABI/physical-trace adapter. The event observer is
   interpreted by the ordinary Kernel.NativeCallAt consumer. It supplies no
   source prefix, argument construction, header allocation, birth or SDK success. *)
Record gateway_native_row_runtime {World Event} (backend : gateway_backend World Event)
    (process position : World -> nat) builders genuine actions_view attributes_view
    (rows : World -> Event -> option (nat * ND.LeanCage_Host_NativeCode_CallRow)) : Prop := {
  gateway_native_actor_ambient : forall before world after next,
    gateway_interference backend before world after next ->
    process next = process world /\ (position world <= position next)%nat;
  gateway_native_actor_external : forall ef types result_type convention arguments before world result after next observed,
    gateway_external backend ef types result_type convention arguments before world result after next observed ->
    process next = process world /\ (position world <= position next)%nat;
  gateway_native_actor_builtin : forall ef types arguments before world result after next observed,
    gateway_builtin backend ef types arguments before world result after next observed ->
    process next = process world /\ (position world <= position next)%nat;
  gateway_native_operation_row : forall definition arguments code before world result after next observed,
    gateway_native_operation_inputs builders genuine actions_view attributes_view before world definition arguments code ->
    gateway_runtime_operation backend definition arguments before world result after next observed ->
    exists selected row,
      rows world observed = Some (selected, row) /\
      gateway_native_row_process row = Nat_of_nat (process world) /\
      gateway_native_row_operation row = code /\ (position world <= selected < position next)%nat
}.

Theorem gateway_native_step_actor {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view rows
    (runtime : gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    ge before event after :
  gateway_step backend ge before event after ->
  process (gateway_state_world after) = process (gateway_state_world before) /\
  (position (gateway_state_world before) <= position (gateway_state_world after))%nat.
Proof.
  intro STEP; inversion STEP; subst; cbn [gateway_state_world];
    try (split; [reflexivity |lia]).
  - eapply gateway_native_actor_external; eassumption.
  - eapply gateway_native_actor_builtin; eassumption.
  - eapply gateway_native_actor_ambient; eassumption.
  - eapply gateway_native_actor_external; eassumption.
  - eapply gateway_native_actor_builtin; eassumption.
Qed.

Theorem gateway_native_run_actor {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view rows
    (runtime : gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    ge before events after :
  gateway_steps backend ge before events after ->
  process (gateway_state_world after) = process (gateway_state_world before) /\
  (position (gateway_state_world before) <= position (gateway_state_world after))%nat.
Proof.
  intro RUN; induction RUN; [split; [reflexivity |lia] |].
  destruct (gateway_native_step_actor backend process position builders genuine actions_view attributes_view rows runtime
    ge first observed middle H) as [PROCESS POSITION].
  destruct IHRUN as [REST REMAINING]; split; [congruence |lia].
Qed.

Theorem gateway_actual_spawn_row {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view rows
    (runtime : gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    key initial_memory initial_world events memory world code arguments result after next observed :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world events memory world arguments code ->
  gateway_runtime_operation backend (gateway_spawn_signature gateway_posix_spawn_api) arguments
    memory world result after next observed ->
  exists selected row,
    rows world observed = Some (selected, row) /\
    gateway_native_row_process row = Nat_of_nat (gateway_source_process key) /\
    gateway_native_row_operation row = code /\
    (gateway_source_entry_position key <= selected)%nat /\
    Nat_of_nat (Pos.to_nat (gateway_source_actions key)) <>
      Nat_of_nat (Pos.to_nat (gateway_source_attributes key)).
Proof.
  intros [SOURCE] OPERATION.
  destruct SOURCE as (entry_arguments & environment & temporaries & allocated & blocks & symbols & continuation & ENTRY & ARGUMENTS & PREFIX &
    ACTIONS & ATTRIBUTES & FRESH_ACTIONS & FRESH_ATTRIBUTES & DISTINCT & PROCESS & POSITION & ORIGINAL_INPUT).
  destruct (gateway_native_run_actor backend process position builders genuine actions_view attributes_view rows runtime
    (Clight.globalenv GatewaySource.prog) _ _ _ PREFIX) as [SAME_PROCESS LATER].
  cbn [gateway_state_world] in SAME_PROCESS, LATER.
  assert (INPUTS : gateway_native_operation_inputs builders genuine actions_view attributes_view memory world
    (gateway_spawn_signature gateway_posix_spawn_api) arguments code).
  { eapply gateway_native_spawn_inputs; [reflexivity |exact ORIGINAL_INPUT]. }
  destruct (gateway_native_operation_row _ _ _ _ _ _ _ _ runtime
    (gateway_spawn_signature gateway_posix_spawn_api) arguments code memory world result after next observed
    INPUTS OPERATION)
    as [selected [row [ROW [ACTOR [INPUT ORDER]]]]].
  exists selected, row; split; [exact ROW |]. split.
  - rewrite ACTOR, PROCESS, SAME_PROCESS; reflexivity.
  - split; [exact INPUT |]. split; [lia |].
    intro SAME; apply (f_equal nat_of_Nat) in SAME; repeat rewrite nat2Natid in SAME.
    apply DISTINCT, Pos2Nat.inj; exact SAME.
Qed.
