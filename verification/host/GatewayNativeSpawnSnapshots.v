(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Observe full fork/exec tables of one actual
   SDK call, independently of its reply. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayNativeImport GatewayNativeWords GatewayNativeRows GatewayNativeReferences
  GatewayNativeStreamObservation GatewayNativeSpawnOperands GatewayNativeSourceBinding GatewaySpawnProcess GatewaySpawnActions
  GatewayErrorRuntime GatewayNativeFullTables GatewaySpawnCall GatewaySpawnResources GatewaySpawnDescriptors
  GatewaySpawnPrivateAliases.
Import ListNotations.
Local Close Scope lean_scope.
Module ND := GatewayNativeImport.

(* A capture describes the actual six input operands. It supplies no successful
   SDK return, child liveness, channel privacy, or future execution. *)
Record gateway_native_birth_capture {World} (builders : World -> gateway_spawn_builders)
    memory world (arguments : list Values.val) (birth : gateway_child_birth) : Prop := {
  gateway_birth_capture_inputs : exists child path actions attributes argv environment,
    arguments = [child; path; actions; attributes; argv; environment] /\
    gateway_error_cstring memory path (gateway_child_path birth) /\
    gateway_spawn_vector memory argv (gateway_child_arguments birth) /\
    gateway_spawn_vector memory environment (gateway_child_environment birth) /\
    gateway_builder_actions (builders world) = Some (actions, gateway_child_actions birth) /\
    gateway_builder_attributes (builders world) = Some (attributes, gateway_child_attributes birth)
}.

Definition gateway_native_execution_code (execution : gateway_child_exec) :=
  ND.LeanCage_Host_NativeCode_Operation_exec (ND.LeanCage_Host_NativeCode_Exec_mk
    (gateway_native_bytes (gateway_exec_path execution))
    (gateway_native_byte_vectors (gateway_exec_arguments execution))
    (gateway_native_byte_vectors (gateway_exec_environment execution))).

(* Pending/executing identify an internal operation of the SAME SDK input snapshot.
   They use stored global rows; equal opcodes or later child execs cannot replace
   that causal observation. No SDK reply is required. *)
Record gateway_native_spawn_snapshot_runtime {World}
    builders genuine actions_view attributes_view
    (births : World -> nat -> option gateway_child_birth)
    (executed : World -> nat -> gateway_child_exec -> Prop)
    (samples : World -> nat -> option ND.LeanCage_Host_NativeCode_CallRow)
    (pending : list Values.val -> mem -> World -> World -> nat -> ND.LeanCage_Host_NativeCode_CallRow -> Prop)
    (executing : list Values.val -> mem -> World -> nat -> World -> nat -> ND.LeanCage_Host_NativeCode_CallRow -> Prop)
    : Prop := {
  gateway_pending_birth_snapshot : forall memory world arguments code current selected row child,
    gateway_native_spawn_operands builders genuine actions_view attributes_view memory world arguments code ->
    pending arguments memory world current selected row -> samples current selected = Some row ->
    gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_created (Nat_of_nat child) ->
    exists birth, births current child = Some birth /\
      gateway_native_birth_capture builders memory world arguments birth /\
      gateway_native_full_table_view (gateway_child_inherited birth) (gateway_native_row_input row);
  gateway_selected_exec_snapshot : forall memory world arguments code born birth_position birth_row child birth
      current selected row image,
    gateway_native_spawn_operands builders genuine actions_view attributes_view memory world arguments code ->
    pending arguments memory world born birth_position birth_row -> samples born birth_position = Some birth_row ->
    gateway_native_row_product birth_row = ND.LeanCage_Host_NativeCode_Product_created (Nat_of_nat child) ->
    births born child = Some birth -> gateway_native_birth_capture builders memory world arguments birth ->
    gateway_native_full_table_view (gateway_child_inherited birth) (gateway_native_row_input birth_row) ->
    executing arguments memory world child current selected row -> samples current selected = Some row ->
    gateway_native_row_process row = Nat_of_nat child ->
    gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_executed (Nat_of_nat image) ->
    exists execution, births current child = Some birth /\ executed current child execution /\
      gateway_exec_from_birth birth execution /\ gateway_exec_image_object execution = image /\
      gateway_native_row_operation row = gateway_native_execution_code execution /\
      gateway_native_full_table_view (gateway_exec_descriptors execution) (gateway_native_row_output row)
}.

Lemma gateway_native_capture_actions {World} (builders : World -> gateway_spawn_builders)
    memory world blocks symbols actions attributes birth plan arguments :
  arguments = gateway_spawn_call_values blocks symbols actions attributes ->
  gateway_builder_actions (builders world) = Some (Vptr actions Ptrofs.zero, plan) ->
  gateway_native_birth_capture builders memory world arguments birth -> gateway_child_actions birth = plan.
Proof.
  intros ARGUMENTS ACTUAL [CAPTURE].
  destruct CAPTURE as (child & path & action_pointer & attribute_pointer & argv & environment & VALUES & PATH & ARGV & ENV & ACTIONS & ATTRIBUTES).
  rewrite ARGUMENTS in VALUES; unfold gateway_spawn_call_values in VALUES.
  inversion VALUES; subst action_pointer.
  rewrite ACTUAL in ACTIONS; inversion ACTIONS; reflexivity.
Qed.

(* Keep the exact original source key and pending prefix as evidence. No helper
   return, SDK acknowledgement, child birth before entry, or safe-role input is used. *)
Theorem gateway_actual_source_fork_snapshot {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view births executed samples pending executing
    (runtime : gateway_native_spawn_snapshot_runtime builders genuine actions_view attributes_view
      births executed samples pending executing)
    key initial_memory initial_world source_events memory world arguments code current selected row child :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world source_events memory world arguments code ->
  pending arguments memory world current selected row -> samples current selected = Some row ->
  gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_created (Nat_of_nat child) ->
  exists birth,
    gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
      initial_memory initial_world source_events memory world arguments code /\
    births current child = Some birth /\ gateway_native_birth_capture builders memory world arguments birth /\
    gateway_native_full_table_view (gateway_child_inherited birth) (gateway_native_row_input row).
Proof.
  intros SOURCE OBSERVED ROW PRODUCT.
  pose proof SOURCE as [ENTRY].
  destruct ENTRY as (entry_arguments & environment & temporaries & allocated & blocks & symbols & continuation &
    ACTUAL_ENTRY & VALUES & PREFIX & ACTIONS & ATTRIBUTES & FRESH_ACTIONS & FRESH_ATTRIBUTES & DISTINCT & PROCESS & POSITION & INPUTS).
  destruct (gateway_pending_birth_snapshot _ _ _ _ _ _ _ _ _ runtime memory world arguments code current selected row child
    INPUTS OBSERVED ROW PRODUCT) as (birth & STORED & CAPTURE & FULL).
  exists birth; split; [exact SOURCE |]. split; [exact STORED |]. split; assumption.
Qed.

Lemma gateway_native_source_capture_actions {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view key initial_memory initial_world source_events
    memory world arguments code birth plan :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world source_events memory world arguments code ->
  gateway_builder_actions (builders world) = Some (Vptr (gateway_source_actions key) Ptrofs.zero, plan) ->
  gateway_native_birth_capture builders memory world arguments birth -> gateway_child_actions birth = plan.
Proof.
  intros [SOURCE] ACTIONS CAPTURE.
  destruct SOURCE as (entry_arguments & environment & temporaries & allocated & blocks & symbols & continuation &
    ENTRY & VALUES & PREFIX & LOCAL_ACTIONS & LOCAL_ATTRIBUTES & FRESH_ACTIONS & FRESH_ATTRIBUTES & DISTINCT & PROCESS & POSITION & INPUTS).
  eapply gateway_native_capture_actions; [exact VALUES |exact ACTIONS |exact CAPTURE].
Qed.

Theorem gateway_actual_source_exec_snapshot {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view births executed samples pending executing
    (runtime : gateway_native_spawn_snapshot_runtime builders genuine actions_view attributes_view
      births executed samples pending executing)
    key initial_memory initial_world source_events memory world arguments code born birth_position birth_row child
    current selected row image plan :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world source_events memory world arguments code ->
  gateway_builder_actions (builders world) = Some (Vptr (gateway_source_actions key) Ptrofs.zero, plan) ->
  pending arguments memory world born birth_position birth_row -> samples born birth_position = Some birth_row ->
  gateway_native_row_product birth_row = ND.LeanCage_Host_NativeCode_Product_created (Nat_of_nat child) ->
  executing arguments memory world child current selected row -> samples current selected = Some row ->
  gateway_native_row_process row = Nat_of_nat child ->
  gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_executed (Nat_of_nat image) ->
  exists birth execution,
    gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
      initial_memory initial_world source_events memory world arguments code /\
    births born child = Some birth /\ births current child = Some birth /\ executed current child execution /\
    gateway_native_birth_capture builders memory world arguments birth /\ gateway_child_actions birth = plan /\
    gateway_native_full_table_view (gateway_child_inherited birth) (gateway_native_row_input birth_row) /\
    gateway_exec_from_birth birth execution /\ gateway_exec_image_object execution = image /\
    gateway_native_row_operation row = gateway_native_execution_code execution /\
    gateway_native_full_table_view (gateway_exec_descriptors execution) (gateway_native_row_output row).
Proof.
  intros SOURCE ACTIONS OBSERVED BIRTH_ROW CREATED EXECUTING ROW PROCESS IMAGE.
  destruct (gateway_actual_source_fork_snapshot backend process position builders genuine actions_view attributes_view
    births executed samples pending executing runtime key initial_memory initial_world source_events memory world arguments code
    born birth_position birth_row child SOURCE OBSERVED BIRTH_ROW CREATED)
    as (birth & SOURCE_AGAIN & STORED & CAPTURE & FULL).
  assert (PLAN : gateway_child_actions birth = plan).
  { eapply gateway_native_source_capture_actions; [exact SOURCE |exact ACTIONS |exact CAPTURE]. }
  pose proof SOURCE as [ENTRY].
  destruct ENTRY as (entry_arguments & environment & temporaries & allocated & blocks & symbols & continuation &
    ACTUAL_ENTRY & VALUES & PREFIX & LOCAL_ACTIONS & LOCAL_ATTRIBUTES & FRESH_ACTIONS & FRESH_ATTRIBUTES & DISTINCT & ACTOR & POSITION & INPUTS).
  destruct (gateway_selected_exec_snapshot _ _ _ _ _ _ _ _ _ runtime memory world arguments code born birth_position
    birth_row child birth current selected row image INPUTS OBSERVED BIRTH_ROW CREATED STORED CAPTURE FULL
    EXECUTING ROW PROCESS IMAGE) as (execution & RETAINED & EXECUTED & FROM_BIRTH & ACTUAL_IMAGE & CODE & EXEC_TABLE).
  exists birth, execution.
  split; [exact SOURCE |]. split; [exact STORED |]. split; [exact RETAINED |]. split; [exact EXECUTED |].
  split; [exact CAPTURE |]. split; [exact PLAN |]. split; [exact FULL |]. split; [exact FROM_BIRTH |].
  split; [exact ACTUAL_IMAGE |]. split; assumption.
Qed.

Theorem gateway_source_snapshot_excludes_caller {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions_view attributes_view key initial_memory initial_world source_events
    memory world arguments code birth execution input output data_peer control_peer data control object :
  gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view key
    initial_memory initial_world source_events memory world arguments code ->
  gateway_builder_actions (builders world) = Some (Vptr (gateway_source_actions key) Ptrofs.zero,
    gateway_private_spawn_plan data_peer control_peer) ->
  gateway_native_birth_capture builders memory world arguments birth ->
  gateway_native_full_table_view (gateway_child_inherited birth) input ->
  gateway_exec_from_birth birth execution -> gateway_native_full_table_view (gateway_exec_descriptors execution) output ->
  (4 <= data_peer)%Z -> (4 <= control_peer)%Z ->
  gateway_native_lease_at input data_peer data -> gateway_native_lease_at input control_peer control ->
  gateway_resource_object (gateway_descriptor_object data) <> object ->
  gateway_resource_object (gateway_descriptor_object control) <> object ->
  gateway_aliases_closeexec (fun endpoint => gateway_resource_object endpoint = object) (gateway_child_inherited birth) ->
  forall descriptor handle, (0 <= descriptor <= Int.max_signed)%Z ->
    gateway_native_reference_handles output (Nat_of_nat (Z.to_nat descriptor)) = ND.Option_some_inst1 _ handle ->
    ND.LeanCage_Host_NativeCode_Handle_object handle <> Nat_of_nat object.
Proof.
  intros SOURCE ACTIONS CAPTURE FORK EXECUTED OUTPUT DATA_BOUND CONTROL_BOUND DATA CONTROL DATA_PUBLIC CONTROL_PUBLIC CLOSED.
  eapply gateway_native_exec_full_table_excludes with (birth := birth) (execution := execution)
    (data_peer := data_peer) (control_peer := control_peer) (data := data) (control := control); try eassumption.
  - eapply gateway_native_source_capture_actions; [exact SOURCE |exact ACTIONS |exact CAPTURE].
  - eapply gateway_native_full_table_source_lease; [exact FORK |exact DATA].
  - eapply gateway_native_full_table_source_lease; [exact FORK |exact CONTROL].
Qed.
