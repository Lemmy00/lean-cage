(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Real entry allocation and setup bind the original pending native row. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewaySpawnActions GatewayPassiveResources
  GatewayBuilderHistory GatewayBuilderScopes GatewayExchangeEntry GatewayExchangePrepared GatewayExchangeEntryPrepared
  GatewayExchangeInitialized GatewayExchangeLaunch GatewayExchangeSDK GatewayExchangeFlagContext
  GatewayExchangeScope GatewayExchangeStorage GatewayLocalRuntime
  GatewayCallerBuffers GatewayCallerFamily GatewaySDKInputs GatewaySpawnVectorMemory GatewaySpawnVectors
  GatewaySpawnVectorStores GatewayVectorCells GatewaySpawnCall GatewayContexts GatewayNativeImport
  GatewayNativeRows GatewayNativeReferences GatewayNativeSpawnOperands GatewayNativeSourceBinding GatewayNativeSourceLeases
  GatewayPendingNativeRows GatewayExchangeNativeSource GatewaySpawnParentContext GatewayLaunchStrings GatewayBufferReference.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module NP := GatewayNativeImport.

Section NativeEntry.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option Values.val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop)
    (registry:World->gateway_builder_registry)(genuine:block->block->mem->World->Prop)
    (footprint:block->block->World->block->Z->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (passive:gateway_passive_resource_runtime backend resources).
Hypothesis SDK:forall actions attributes,actions<>attributes->gateway_spawn_builder_runtime backend io native stable discipline resources
  (gateway_scoped_builders registry actions attributes)(genuine actions attributes)(footprint actions attributes).
Hypothesis HISTORY:forall actions attributes,actions<>attributes->gateway_builder_history_runtime backend native
  (gateway_scoped_builders registry actions attributes)actions attributes.
Hypothesis INITIALIZERS:forall actions attributes,actions<>attributes->gateway_spawn_initializer_runtime backend io native stable discipline resources
  (gateway_scoped_builders registry actions attributes)(genuine actions attributes)(footprint actions attributes)actions attributes.
Context(process position:World->nat)
  (actions_view:World->Values.val->NP.List_inst1 NP.LeanCage_Host_NativeCode_FileAction->Prop)
  (attributes_view:World->Values.val->NP.LeanCage_Host_NativeCode_SpawnAttributes->Prop)
  (rows:World->Event->option(nat*NP.LeanCage_Host_NativeCode_CallRow))
  (pending:list Values.val->mem->World->World->nat->NP.LeanCage_Host_NativeCode_CallRow->Prop).
Hypothesis RECORDING:forall actions attributes,actions<>attributes->gateway_native_row_runtime backend process position
  (gateway_scoped_builders registry actions attributes)(genuine actions attributes)actions_view attributes_view rows.
Hypothesis VIEW:forall actions attributes,actions<>attributes->gateway_native_sdk_view
  (gateway_scoped_builders registry actions attributes)(genuine actions attributes)actions_view attributes_view.
Hypothesis PENDING:forall actions attributes,actions<>attributes->gateway_pending_spawn_runtime process position
  (gateway_scoped_builders registry actions attributes)(genuine actions attributes)actions_view attributes_view resources pending.
Context(references:gateway_native_reference_runtime backend resources rows).

(* The initialized regional strings are raw loader bytes in the SAME initial
   memory. The actual native caller frame carries them to the pending call. *)
Theorem actual_exchange_entry_pending_native initial_memory allocated environment temporaries entry_arguments initial_world readonly
    events target_arguments target_continuation target_memory target_world engine_bytes:
  function_entry2(Clight.globalenv prog)f_host_exchange entry_arguments initial_memory environment temporaries allocated->
  discipline None initial_memory initial_world->gateway_caller_readonly native stable readonly initial_memory initial_world->
  gateway_resource_valid(resources initial_world)->gateway_builder_registry_allocated initial_memory(registry initial_world)->
  gateway_global_launch_strings readonly initial_memory engine_bytes->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries allocated)initial_world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)target_arguments target_continuation target_memory)target_world)->
  exists data control actions attributes blocks symbols data_identity control_identity data_left data_right control_left control_right
    source_prefix suffix memory world called_temps actual_attributes,
    gateway_exchange_storage native stable readonly allocated initial_world environment data control actions attributes blocks symbols /\
    events=source_prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries allocated)initial_world)source_prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)(gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment called_temps Kstop)memory)world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)(gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment called_temps Kstop)memory)world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)target_arguments target_continuation target_memory)target_world) /\
    gateway_sdk_context native stable discipline resources ipc readonly(exchange_selected_block environment)allocated initial_world(resources initial_world)
      data_identity control_identity data control data_left data_right control_left control_right
      (gateway_scoped_builders registry actions attributes)(genuine actions attributes)
      (Some(Vptr actions Ptrofs.zero,exchange_sdk_plan data_right control_right))
      (Some(Vptr attributes Ptrofs.zero,exchange_sdk_attributes))memory world /\
    gateway_native_attribute_fields exchange_sdk_attributes actual_attributes /\
    gateway_native_pending_spawn backend process position(gateway_scoped_builders registry actions attributes)(genuine actions attributes)
      actions_view attributes_view
      {|gateway_source_process:=process initial_world;gateway_source_entry_position:=position initial_world;
        gateway_source_actions:=actions;gateway_source_attributes:=attributes|}
      initial_memory initial_world source_prefix memory world(gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]
        (exchange_sdk_plan data_right control_right)actual_attributes) /\
    forall current selected row,pending(gateway_spawn_call_values blocks symbols actions attributes)memory world current selected row->
      gateway_native_row_process row=Nat_of_nat(process initial_world) /\
      gateway_native_row_operation row=gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]
        (exchange_sdk_plan data_right control_right)actual_attributes /\
      (position initial_world<=selected<position current)%nat /\
      Nat_of_nat(Pos.to_nat actions)<>Nat_of_nat(Pos.to_nat attributes) /\
      Forall(fun lease=>gateway_native_lease_at(gateway_native_row_input row)(fst lease)(snd lease))
        (gateway_parent_ipc_leases ipc data_identity control_identity data_left data_right control_left control_right).
Proof.
  intros ENTRY SIDE READONLY VALID REGISTRY STRINGS RUN.
  assert(ALLOC:alloc_variables(Clight.globalenv prog)empty_env initial_memory(fn_vars f_host_exchange)environment allocated).
  { inversion ENTRY;subst;assumption. }
  destruct(gateway_native_alloc_variables backend io native stable discipline thread_errno thread(Clight.globalenv prog)None
    empty_env initial_memory(fn_vars f_host_exchange)environment allocated initial_world ALLOC SIDE
    (gateway_native_environment_empty native initial_world initial_memory))as[ALLOCATED NATIVE].
  destruct(actual_exchange_allocated_entry_spawn backend io native stable discipline thread_errno resources ipc registry genuine footprint
    thread descriptors passive SDK HISTORY INITIALIZERS initial_memory allocated environment temporaries initial_world readonly events
    target_arguments target_continuation target_memory target_world ALLOC ALLOCATED NATIVE READONLY VALID REGISTRY RUN)
    as(data&control&actions&attributes&blocks&symbols&STORAGE&[FRONTIER]).
  destruct FRONTIER as[loaded guard_prefix body_events guarded guarded_world EVENTS_GUARD QUIET GUARD BODY].
  destruct BODY as[began flags data_identity control_identity data_left data_right control_left control_right prefix suffix memory world
    EVENTS ORDER OBJECTS DATA_LEFT DATA_RIGHT CONTROL_LEFT CONTROL_RIGHT SOURCE CONTEXT VECTORS TAIL].
  assert(HEADERS:actions<>attributes)by(exact(exchange_storage_headers
    native stable readonly allocated initial_world environment data control actions attributes blocks symbols STORAGE)).
  assert(FULL:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries allocated)initial_world)
    (guard_prefix++prefix)(gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
      (gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment(exchange_launch_temps began flags data_right control_right(exchange_entry_temps loaded temporaries))Kstop)
      memory)world)).
  { eapply gateway_steps_append;[exact GUARD|exact SOURCE]. }
  assert(FRAME:Mem.unchanged_on readonly initial_memory memory).
  { pose proof CONTEXT as[[NORMAL[FAMILY REST]]MORE].
    pose proof(exchange_storage_data
      native stable readonly allocated initial_world environment data control actions attributes blocks symbols STORAGE)as DATA.
    destruct(FAMILY data ltac:(exists _pair,(tarray tint 2);exact DATA))as[LIVE[PRIVATE[RO[[CONTENTS PERMISSIONS]HISTORY_REST]]]].
    eapply Mem.unchanged_on_trans;[|exact CONTENTS].
    eapply Mem.unchanged_on_implies;[exact(proj2(proj2(actual_exchange_allocations(Clight.globalenv prog)initial_memory environment allocated ALLOC)))|].
    intros;exact I. }
  destruct(gateway_launch_strings_selected readonly memory engine_bytes environment blocks symbols
    (gateway_global_launch_strings_retained readonly initial_memory memory engine_bytes STRINGS FRAME)
    (exchange_storage_locations
      native stable readonly allocated initial_world environment data control actions attributes blocks symbols STORAGE))as[ENGINE[PATH LOCALE]].
  destruct(gateway_exchange_source_native_pending backend process position(gateway_scoped_builders registry actions attributes)
    (genuine actions attributes)actions_view attributes_view rows resources(RECORDING actions attributes HEADERS)references(VIEW actions attributes HEADERS)
    pending(PENDING actions attributes HEADERS)native stable discipline ipc readonly initial_memory initial_world allocated environment temporaries
    entry_arguments data control actions attributes blocks symbols data_identity control_identity data_left data_right control_left control_right
    (exchange_sdk_plan data_right control_right)exchange_sdk_attributes(guard_prefix++prefix)memory world
    (gateway_spawn_call_cont environment(exchange_launch_temps began flags data_right control_right(exchange_entry_temps loaded temporaries))Kstop)
    engine_bytes ENTRY STORAGE FULL CONTEXT VECTORS ENGINE PATH LOCALE)
    as[actual_attributes[FIELDS[KEY[COMMITTED OBSERVED]]]].
  exists data,control,actions,attributes,blocks,symbols,data_identity,control_identity,data_left,data_right,control_left,control_right,
    (guard_prefix++prefix),suffix,memory,world,
    (exchange_launch_temps began flags data_right control_right(exchange_entry_temps loaded temporaries)),actual_attributes.
  split;[exact STORAGE|]. split;[rewrite EVENTS_GUARD,EVENTS,app_assoc;reflexivity|].
  split;[exact FULL|]. split;[exact TAIL|]. split;[exact CONTEXT|]. split;[exact FIELDS|]. split;assumption.
Qed.
End NativeEntry.
