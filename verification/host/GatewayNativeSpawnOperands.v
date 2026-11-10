(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Real pending spawn operands cross the shared data boundary before any reply. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayNativeImport GatewayNativeWords GatewaySpawnActions GatewaySpawnDescriptors
  GatewaySpawnVectors GatewaySpawnVectorValues GatewaySpawnVectorMemory GatewayVectorCells GatewaySpawnCall
  GatewaySpawnProcess GatewaySDKInputs GatewayErrorRuntime GatewayExchangeScope.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.
Local Opaque Nat_of_nat Z.to_nat.

Definition gateway_native_action (action : gateway_spawn_action) : ND.LeanCage_Host_NativeCode_FileAction :=
  match action with
  | gateway_spawn_dup source target => ND.LeanCage_Host_NativeCode_FileAction_duplicate
      (gateway_native_int (Int.repr source)) (gateway_native_int (Int.repr target))
  | gateway_spawn_closefrom minimum => ND.LeanCage_Host_NativeCode_FileAction_closeFrom
      (gateway_native_int (Int.repr minimum))
  end.
Fixpoint gateway_native_actions (actions : list gateway_spawn_action)
    : ND.List_inst1 ND.LeanCage_Host_NativeCode_FileAction := match actions with
  | [] => ND.List_nil_inst1 _
  | action :: rest => ND.List_cons_inst1 _ (gateway_native_action action) (gateway_native_actions rest)
  end.

Definition gateway_native_attribute_fields (settings : gateway_spawn_attributes)
    (actual : ND.LeanCage_Host_NativeCode_SpawnAttributes) : Prop :=
  match actual with ND.LeanCage_Host_NativeCode_SpawnAttributes_mk flags group mask defaults policy priority =>
    flags = gateway_native_int (gateway_attribute_flags settings) /\
    group = gateway_native_int (gateway_attribute_group settings)
  end.

(* A representation view of one already genuine, live SDK object. Source setup
   supplies that object/shadow; this view constructs no application argument,
   private channel, birth, execution, FD lease or caller lifetime. *)
Record gateway_native_sdk_view {World} (builders : World -> gateway_spawn_builders)
    (genuine : mem -> World -> Prop)
    (actions : World -> Values.val -> ND.List_inst1 ND.LeanCage_Host_NativeCode_FileAction -> Prop)
    (attributes : World -> Values.val -> ND.LeanCage_Host_NativeCode_SpawnAttributes -> Prop) : Prop := {
  gateway_native_sdk_actions : forall memory world pointer plan,
    genuine memory world -> gateway_builder_actions (builders world) = Some (pointer, plan) ->
    actions world pointer (gateway_native_actions plan);
  gateway_native_sdk_attributes : forall memory world pointer settings,
    genuine memory world -> gateway_builder_attributes (builders world) = Some (pointer, settings) ->
    exists actual, attributes world pointer actual /\ gateway_native_attribute_fields settings actual
}.

Definition gateway_native_spawn_code path arguments environment plan attributes :=
  ND.LeanCage_Host_NativeCode_Operation_spawn
    (ND.LeanCage_Host_NativeCode_Spawn_mk (gateway_native_bytes path)
      (gateway_native_byte_vectors arguments) (gateway_native_byte_vectors environment)
      (gateway_native_actions plan) attributes).

Record gateway_native_spawn_operands {World} builders genuine actions attributes memory (world : World)
    (values : list Values.val) (code : ND.LeanCage_Host_NativeCode_Operation) : Prop := {
  gateway_native_spawn_arguments : exists child path action_object attribute_object argument_array environment_array
      path_bytes argument_bytes environment_bytes plan settings actual_attributes,
    values = [child; path; action_object; attribute_object; argument_array; environment_array] /\
    gateway_error_cstring memory path path_bytes /\
    gateway_spawn_vector memory argument_array argument_bytes /\
    gateway_spawn_vector memory environment_array environment_bytes /\ genuine memory world /\
    gateway_builder_actions (builders world) = Some (action_object, plan) /\
    gateway_builder_attributes (builders world) = Some (attribute_object, settings) /\
    actions world action_object (gateway_native_actions plan) /\
    attributes world attribute_object actual_attributes /\
    gateway_native_attribute_fields settings actual_attributes /\
    code = gateway_native_spawn_code path_bytes argument_bytes environment_bytes plan actual_attributes
}.

Theorem gateway_actual_spawn_native_operands {World} native stable discipline resources ipc builders genuine actions_view attributes_view
    (sdk : @gateway_native_sdk_view World builders genuine actions_view attributes_view)
    readonly reference owner environment data control actions attributes blocks symbols data_identity control_identity
    data_left data_right control_left control_right plan settings memory world engine_bytes :
  gateway_sdk_context native stable discipline resources ipc readonly (exchange_selected_block environment)
    reference owner (resources owner) data_identity control_identity data control data_left data_right control_left control_right
    builders genuine (Some (Vptr actions Ptrofs.zero, plan)) (Some (Vptr attributes Ptrofs.zero, settings)) memory world ->
  Forall (gateway_vector_loaded memory) (gateway_spawn_cell_plan blocks symbols) ->
  gateway_error_cstring memory (Vptr (spawn_engine_symbol symbols) Ptrofs.zero) engine_bytes ->
  gateway_error_cstring memory (Vptr (spawn_path_symbol symbols) Ptrofs.zero) spawn_path_bytes ->
  gateway_error_cstring memory (Vptr (spawn_locale_symbol symbols) Ptrofs.zero) spawn_locale_bytes ->
  exists actual_attributes,
    gateway_native_attribute_fields settings actual_attributes /\
    gateway_native_spawn_operands builders genuine actions_view attributes_view memory world
      (gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_native_spawn_code engine_bytes [engine_bytes] [spawn_path_bytes; spawn_locale_bytes] plan actual_attributes).
Proof.
  intros [_ [GENUINE [ACTIONS ATTRIBUTES]]] LOADED ENGINE PATH LOCALE.
  destruct (gateway_spawn_vectors_from_cells memory blocks symbols engine_bytes LOADED ENGINE PATH LOCALE)
    as [ARGUMENTS ENVIRONMENT].
  destruct (gateway_native_sdk_attributes builders genuine actions_view attributes_view sdk
    memory world (Vptr attributes Ptrofs.zero) settings GENUINE ATTRIBUTES)
    as [actual [REPRESENTED FIELDS]].
  exists actual; split; [exact FIELDS |]. constructor.
  exists (Vptr (spawn_child_block blocks) Ptrofs.zero), (Vptr (spawn_engine_symbol symbols) Ptrofs.zero),
    (Vptr actions Ptrofs.zero), (Vptr attributes Ptrofs.zero), (Vptr (spawn_arguments_block blocks) Ptrofs.zero),
    (Vptr (spawn_environment_block blocks) Ptrofs.zero), engine_bytes, [engine_bytes],
    [spawn_path_bytes; spawn_locale_bytes], plan, settings, actual.
  split; [reflexivity |]. split; [exact ENGINE |]. split; [exact ARGUMENTS |].
  split; [exact ENVIRONMENT |]. split; [exact GENUINE |]. split; [exact ACTIONS |].
  split; [exact ATTRIBUTES |]. split.
  - eapply gateway_native_sdk_actions; [exact sdk |exact GENUINE |exact ACTIONS].
  - split; [exact REPRESENTED |]. split; [exact FIELDS |reflexivity].
Qed.
