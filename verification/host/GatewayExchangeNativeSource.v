(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: A real pending exchange call binds its actual native row and IPC leases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewaySpawnABI GatewaySpawnResources GatewaySpawnCall
  GatewaySDKInputs GatewayExchangeEntry GatewayExchangePrepared GatewayExchangeStorage GatewayExchangeScope GatewaySpawnActions
  GatewayPairContext GatewayConnectionResources GatewaySpawnVectorMemory GatewaySpawnVectors GatewayVectorCells GatewayErrorRuntime
  GatewayNativeImport GatewayNativeSpawnOperands GatewayNativeSourceBinding GatewayNativeRows GatewayNativeReferences GatewayNativeSourceLeases
  GatewaySpawnParentContext GatewayPendingNativeRows.
Import ListNotations.
Local Close Scope lean_scope.
Module EN := GatewayNativeImport.

Theorem gateway_exchange_source_native_call {World Event}(backend:gateway_backend World Event)
    process position builders genuine actions_view attributes_view rows resources
    (recording:gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    (references:gateway_native_reference_runtime backend resources rows)
    (view:gateway_native_sdk_view builders genuine actions_view attributes_view)
    native stable discipline ipc readonly initial_memory initial_world allocated environment temporaries entry_arguments
    data control actions attributes blocks symbols data_identity control_identity data_left data_right control_left control_right
    plan settings events memory world continuation engine_bytes:
  function_entry2(Clight.globalenv prog)f_host_exchange entry_arguments initial_memory environment temporaries allocated->
  gateway_exchange_storage native stable readonly allocated initial_world environment data control actions attributes blocks symbols->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries allocated)initial_world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
      (gateway_spawn_call_values blocks symbols actions attributes)continuation memory)world)->
  gateway_sdk_context native stable discipline resources ipc readonly(exchange_selected_block environment)allocated initial_world(resources initial_world)
    data_identity control_identity data control data_left data_right control_left control_right builders genuine
    (Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings))memory world->
  Forall(gateway_vector_loaded memory)(gateway_spawn_cell_plan blocks symbols)->
  gateway_error_cstring memory(Vptr(spawn_engine_symbol symbols)Ptrofs.zero)engine_bytes->
  gateway_error_cstring memory(Vptr(spawn_path_symbol symbols)Ptrofs.zero)spawn_path_bytes->
  gateway_error_cstring memory(Vptr(spawn_locale_symbol symbols)Ptrofs.zero)spawn_locale_bytes->
  exists actual_attributes,
    gateway_native_attribute_fields settings actual_attributes /\
    gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view
      {|gateway_source_process:=process initial_world;gateway_source_entry_position:=position initial_world;
        gateway_source_actions:=actions;gateway_source_attributes:=attributes|}
      initial_memory initial_world events memory world(gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]plan actual_attributes) /\
    forall result after next observed,
      gateway_runtime_operation backend(gateway_spawn_signature gateway_posix_spawn_api)(gateway_spawn_call_values blocks symbols actions attributes)
        memory world result after next observed->
      exists selected_row row,
        rows world observed=Some(selected_row,row) /\
        gateway_native_row_process row=Nat_of_nat(process initial_world) /\
        gateway_native_row_operation row=gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]plan actual_attributes /\
        (position initial_world<=selected_row)%nat /\
        Nat_of_nat(Pos.to_nat actions)<>Nat_of_nat(Pos.to_nat attributes) /\
        Forall(fun lease=>gateway_native_lease_at(gateway_native_row_input row)(fst lease)(snd lease))
          (gateway_parent_ipc_leases ipc data_identity control_identity data_left data_right control_left control_right).
Proof.
  intros ENTRY STORAGE SOURCE CONTEXT VECTORS ENGINE PATH LOCALE.
  assert(ALLOC:alloc_variables(Clight.globalenv prog)empty_env initial_memory(fn_vars f_host_exchange)environment allocated).
  { inversion ENTRY;subst;assumption. }
  pose proof STORAGE as COPY.
  destruct COPY as[DATA CONTROL ACTIONS ATTRIBUTES DATA_CONTROL ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA ATTRIBUTES_CONTROL HEADERS REST].
  assert(FRESH_ACTIONS:~Mem.valid_block initial_memory actions).
  { eapply actual_exchange_allocated_local_fresh with(identifier:=_actions)(ty:=gateway_actions_type);
      [exact ALLOC|cbn;auto 14|exact ACTIONS]. }
  assert(FRESH_ATTRIBUTES:~Mem.valid_block initial_memory attributes).
  { eapply actual_exchange_allocated_local_fresh with(identifier:=_attributes)(ty:=gateway_attributes_type);
      [exact ALLOC|cbn;auto 14|exact ATTRIBUTES]. }
  destruct(gateway_actual_spawn_native_operands native stable discipline resources ipc builders genuine actions_view attributes_view view
    readonly allocated initial_world environment data control actions attributes blocks symbols data_identity control_identity
    data_left data_right control_left control_right plan settings memory world engine_bytes CONTEXT VECTORS ENGINE PATH LOCALE)
    as[actual_attributes[FIELDS OPERANDS]].
  pose proof(gateway_actual_pending_spawn_key backend process position builders genuine actions_view attributes_view entry_arguments environment temporaries
    initial_memory initial_world allocated events memory world blocks symbols actions attributes continuation
    (gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]plan actual_attributes)
    ENTRY SOURCE ACTIONS ATTRIBUTES FRESH_ACTIONS FRESH_ATTRIBUTES HEADERS OPERANDS)as PENDING.
  exists actual_attributes;split;[exact FIELDS|]. split;[exact PENDING|].
  intros result after next observed OPERATION.
  eapply gateway_actual_spawn_row_leases with
    (key:={|gateway_source_process:=process initial_world;gateway_source_entry_position:=position initial_world;
      gateway_source_actions:=actions;gateway_source_attributes:=attributes|});
    [exact recording|exact references|exact PENDING|exact CONTEXT|exact OPERATION].
Qed.


Theorem gateway_exchange_source_native_pending {World Event}(backend:gateway_backend World Event)
    process position builders genuine actions_view attributes_view rows resources
    (recording:gateway_native_row_runtime backend process position builders genuine actions_view attributes_view rows)
    (references:gateway_native_reference_runtime backend resources rows)
    (view:gateway_native_sdk_view builders genuine actions_view attributes_view)
    pending(primitive:gateway_pending_spawn_runtime process position builders genuine actions_view attributes_view resources pending)
    native stable discipline ipc readonly initial_memory initial_world allocated environment temporaries entry_arguments
    data control actions attributes blocks symbols data_identity control_identity data_left data_right control_left control_right
    plan settings events memory world continuation engine_bytes:
  function_entry2(Clight.globalenv prog)f_host_exchange entry_arguments initial_memory environment temporaries allocated->
  gateway_exchange_storage native stable readonly allocated initial_world environment data control actions attributes blocks symbols->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries allocated)initial_world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
      (gateway_spawn_call_values blocks symbols actions attributes)continuation memory)world)->
  gateway_sdk_context native stable discipline resources ipc readonly(exchange_selected_block environment)allocated initial_world(resources initial_world)
    data_identity control_identity data control data_left data_right control_left control_right builders genuine
    (Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings))memory world->
  Forall(gateway_vector_loaded memory)(gateway_spawn_cell_plan blocks symbols)->
  gateway_error_cstring memory(Vptr(spawn_engine_symbol symbols)Ptrofs.zero)engine_bytes->
  gateway_error_cstring memory(Vptr(spawn_path_symbol symbols)Ptrofs.zero)spawn_path_bytes->
  gateway_error_cstring memory(Vptr(spawn_locale_symbol symbols)Ptrofs.zero)spawn_locale_bytes->
  exists actual_attributes,
    gateway_native_attribute_fields settings actual_attributes /\
    gateway_native_pending_spawn backend process position builders genuine actions_view attributes_view
      {|gateway_source_process:=process initial_world;gateway_source_entry_position:=position initial_world;
        gateway_source_actions:=actions;gateway_source_attributes:=attributes|}
      initial_memory initial_world events memory world(gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]plan actual_attributes) /\
    (forall result after next observed,
      gateway_runtime_operation backend(gateway_spawn_signature gateway_posix_spawn_api)(gateway_spawn_call_values blocks symbols actions attributes)
        memory world result after next observed->
      exists selected_row row,
        rows world observed=Some(selected_row,row) /\
        gateway_native_row_process row=Nat_of_nat(process initial_world) /\
        gateway_native_row_operation row=gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]plan actual_attributes /\
        (position initial_world<=selected_row)%nat /\
        Nat_of_nat(Pos.to_nat actions)<>Nat_of_nat(Pos.to_nat attributes) /\
        Forall(fun lease=>gateway_native_lease_at(gateway_native_row_input row)(fst lease)(snd lease))
          (gateway_parent_ipc_leases ipc data_identity control_identity data_left data_right control_left control_right)) /\
    forall current selected row,
      pending(gateway_spawn_call_values blocks symbols actions attributes)memory world current selected row->
      gateway_native_row_process row=Nat_of_nat(process initial_world) /\
      gateway_native_row_operation row=gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]plan actual_attributes /\
      (position initial_world<=selected<position current)%nat /\
      Nat_of_nat(Pos.to_nat actions)<>Nat_of_nat(Pos.to_nat attributes) /\
      Forall(fun lease=>gateway_native_lease_at(gateway_native_row_input row)(fst lease)(snd lease))
        (gateway_parent_ipc_leases ipc data_identity control_identity data_left data_right control_left control_right).
Proof.
  intros ENTRY STORAGE SOURCE CONTEXT VECTORS ENGINE PATH LOCALE.
  destruct(gateway_exchange_source_native_call backend process position builders genuine actions_view attributes_view rows resources
    recording references view native stable discipline ipc readonly initial_memory initial_world allocated environment temporaries entry_arguments
    data control actions attributes blocks symbols data_identity control_identity data_left data_right control_left control_right plan settings
    events memory world continuation engine_bytes ENTRY STORAGE SOURCE CONTEXT VECTORS ENGINE PATH LOCALE)
    as[actual_attributes[FIELDS[PENDING COMMITTED]]].
  exists actual_attributes;split;[exact FIELDS|]. split;[exact PENDING|]. split;[exact COMMITTED|].
  intros current selected row OBSERVED.
  eapply gateway_actual_pending_spawn_row_leases with
    (key:={|gateway_source_process:=process initial_world;gateway_source_entry_position:=position initial_world;
      gateway_source_actions:=actions;gateway_source_attributes:=attributes|});
    [exact recording|exact primitive|exact PENDING|exact CONTEXT|exact OBSERVED].
Qed.
