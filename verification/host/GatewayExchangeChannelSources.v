(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Real entry allocation and setup bind the
   original pending native row. *)
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
From HostGateway Require Import GatewayPairCopyout GatewayPairContext GatewayExchangeOriginSetup.
From HostGateway Require Import GatewayChannelSourceScope GatewayChannelCodeProducer GatewayChannelPairSource
  GatewayChannelPairSlices GatewayChannelExecSource GatewayNativeSpawnSnapshots GatewayNativeStreamObservation GatewayPairSource
  GatewayNativeFullTables GatewaySpawnProcess GatewayExchangeOriginPrepared GatewayNativePairObservation.
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

Context (pair_observation : gateway_native_pair_runtime backend resources ipc rows)
  (births : World -> nat -> option gateway_child_birth)
  (executed : World -> nat -> gateway_child_exec -> Prop)
  (samples : World -> nat -> option NP.LeanCage_Host_NativeCode_CallRow)
  (executing : list Values.val -> mem -> World -> nat -> World -> nat -> NP.LeanCage_Host_NativeCode_CallRow -> Prop).
Hypothesis SNAPSHOTS : forall actions attributes, actions <> attributes -> gateway_native_spawn_snapshot_runtime
  (gateway_scoped_builders registry actions attributes) (genuine actions attributes) actions_view attributes_view
  births executed samples pending executing.
Theorem actual_exchange_entry_channel_sources initial_memory allocated environment temporaries entry_arguments initial_world readonly
    events target_arguments target_continuation target_memory target_world engine_bytes:
  function_entry2(Clight.globalenv prog)f_host_exchange entry_arguments initial_memory environment temporaries allocated->
  discipline None initial_memory initial_world->gateway_caller_readonly native stable readonly initial_memory initial_world->
  gateway_resource_valid(resources initial_world)->gateway_builder_registry_allocated initial_memory(registry initial_world)->
  gateway_global_launch_strings readonly initial_memory engine_bytes->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries allocated)initial_world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)target_arguments target_continuation target_memory)target_world)->
  exists data control actions attributes blocks symbols data_identity control_identity data_left data_right control_left control_right
    source_prefix suffix memory world called_temps actual_attributes
    (storage : gateway_channel_storage environment initial_memory allocated)
    data_use control_use data_position control_position data_prefix control_prefix data_memory control_memory
    data_world control_world data_event control_event,
    gateway_exchange_storage native stable readonly allocated initial_world environment data control actions attributes blocks symbols /\
    gateway_copyout_pairs_slice_ordered backend resources ipc data control
      (State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries allocated)initial_world
      source_prefix
      (Callstate(gateway_spawn_signature gateway_posix_spawn_api)(gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment called_temps Kstop)memory)world data_identity control_identity /\
    pair_right_object ipc data_identity <> pair_right_object ipc control_identity /\
    4 <= data_left /\ 4 <= data_right /\ 4 <= control_left /\ 4 <= control_right /\
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
    NP.LeanCage_Host_ChannelCode_PairUse_invocation data_use =
      gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world) /\
    NP.LeanCage_Host_ChannelCode_PairUse_invocation control_use =
      gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world) /\
    NP.LeanCage_Host_ChannelCode_Invocation_key
      (gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world)) =
      gateway_native_shared_key {|gateway_source_process:=process initial_world;gateway_source_entry_position:=position initial_world;
        gateway_source_actions:=actions;gateway_source_attributes:=attributes|} /\
    gateway_channel_pair_kind_of data_use = gateway_channel_kind gateway_channel_data_pair /\
    gateway_channel_pair_kind_of control_use = gateway_channel_kind gateway_channel_control_pair /\
    NP.LeanCage_Host_ChannelCode_PairUse_position data_use = Nat_of_nat data_position /\
    NP.LeanCage_Host_ChannelCode_PairUse_position control_use = Nat_of_nat control_position /\
    rows data_world data_event = Some (data_position, NP.LeanCage_Host_ChannelCode_PairUse_row data_use) /\
    rows control_world control_event = Some (control_position, NP.LeanCage_Host_ChannelCode_PairUse_row control_use) /\
    gateway_channel_pending_pair backend process position
      (gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world)) gateway_channel_data_pair
      initial_memory initial_world data_prefix data_memory data_world (pair_socket_arguments data Ptrofs.zero) /\
    gateway_channel_pending_pair backend process position
      (gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world)) gateway_channel_control_pair
      initial_memory initial_world control_prefix control_memory control_world (pair_socket_arguments control Ptrofs.zero) /\
    (position initial_world <= data_position < position world)%nat /\
    (position initial_world <= control_position < position world)%nat /\
    NP.LeanCage_Host_ChannelCode_PairUse_leftObject data_use = Nat_of_nat (pair_left_object ipc data_identity) /\
    NP.LeanCage_Host_ChannelCode_PairUse_rightObject data_use = Nat_of_nat (pair_right_object ipc data_identity) /\
    NP.LeanCage_Host_ChannelCode_PairUse_leftDescription data_use = Nat_of_nat (pair_left_description ipc data_identity) /\
    NP.LeanCage_Host_ChannelCode_PairUse_rightDescription data_use = Nat_of_nat (pair_right_description ipc data_identity) /\
    NP.LeanCage_Host_ChannelCode_PairUse_leftObject control_use = Nat_of_nat (pair_left_object ipc control_identity) /\
    NP.LeanCage_Host_ChannelCode_PairUse_rightObject control_use = Nat_of_nat (pair_right_object ipc control_identity) /\
    NP.LeanCage_Host_ChannelCode_PairUse_leftDescription control_use = Nat_of_nat (pair_left_description ipc control_identity) /\
    NP.LeanCage_Host_ChannelCode_PairUse_rightDescription control_use = Nat_of_nat (pair_right_description ipc control_identity) /\
    gateway_channel_pair_checked data_use /\ gateway_channel_pair_checked control_use /\
    (forall born birth_position birth_row child current selected row image,
      pending (gateway_spawn_call_values blocks symbols actions attributes) memory world born birth_position birth_row ->
      samples born birth_position = Some birth_row ->
      gateway_native_row_product birth_row = NP.LeanCage_Host_NativeCode_Product_created (Nat_of_nat child) ->
      executing (gateway_spawn_call_values blocks symbols actions attributes) memory world child current selected row ->
      samples current selected = Some row -> gateway_native_row_process row = Nat_of_nat child ->
      gateway_native_row_product row = NP.LeanCage_Host_NativeCode_Product_executed (Nat_of_nat image) ->
      exists birth execution,
        births born child = Some birth /\ births current child = Some birth /\ executed current child execution /\
        gateway_exec_from_birth birth execution /\ gateway_exec_image_object execution = image /\
        gateway_native_row_operation row = gateway_native_execution_code execution /\
        gateway_native_full_table_view (gateway_exec_descriptors execution) (gateway_native_row_output row) /\
        gateway_native_channels_checked (gateway_native_row_output row)
          (NP.LeanCage_Host_ChannelCode_PairUse_rightObject data_use)
          (NP.LeanCage_Host_ChannelCode_PairUse_rightObject control_use)) /\
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
  destruct (actual_exchange_entry_pair_origins backend io native stable discipline thread_errno resources ipc registry genuine footprint
    thread descriptors passive SDK HISTORY INITIALIZERS process position actions_view attributes_view rows pending RECORDING VIEW PENDING
    references initial_memory allocated environment temporaries entry_arguments initial_world readonly events target_arguments
    target_continuation target_memory target_world engine_bytes ENTRY SIDE READONLY VALID REGISTRY STRINGS RUN)
    as (data & control & actions & attributes & blocks & symbols & data_identity & control_identity & data_left & data_right &
      control_left & control_right & source_prefix & suffix & memory & world & called_temps & actual_attributes &
      STORAGE & ORIGINS & SEPARATE & DATA_LEFT_BOUND & DATA_RIGHT_BOUND & CONTROL_LEFT_BOUND & CONTROL_RIGHT_BOUND & EVENTS & PREFIX & SUFFIX & CONTEXT & FIELDS & KEY & OBSERVED).
  assert (HEADERS : actions <> attributes) by (exact (exchange_storage_headers
    native stable readonly allocated initial_world environment data control actions attributes blocks symbols STORAGE)).
  destruct (actual_exchange_channel_storage (Clight.globalenv prog) entry_arguments initial_memory environment temporaries allocated ENTRY)
    as [storage].
  assert (DATA_STORAGE : gateway_channel_data _ _ _ storage = data).
  { pose proof (gateway_channel_data_local _ _ _ storage) as SAME.
    rewrite (exchange_storage_data native stable readonly allocated initial_world environment data control actions attributes blocks symbols STORAGE)
      in SAME; inversion SAME; reflexivity. }
  assert (CONTROL_STORAGE : gateway_channel_control _ _ _ storage = control).
  { pose proof (gateway_channel_control_local _ _ _ storage) as SAME.
    rewrite (exchange_storage_control native stable readonly allocated initial_world environment data control actions attributes blocks symbols STORAGE)
      in SAME; inversion SAME; reflexivity. }
  assert (ACTIONS_STORAGE : gateway_channel_actions _ _ _ storage = actions).
  { pose proof (gateway_channel_actions_local _ _ _ storage) as SAME.
    rewrite (exchange_storage_actions native stable readonly allocated initial_world environment data control actions attributes blocks symbols STORAGE)
      in SAME; inversion SAME; reflexivity. }
  assert (ATTRIBUTES_STORAGE : gateway_channel_attributes _ _ _ storage = attributes).
  { pose proof (gateway_channel_attributes_local _ _ _ storage) as SAME.
    rewrite (exchange_storage_attributes native stable readonly allocated initial_world environment data control actions attributes blocks symbols STORAGE)
      in SAME; inversion SAME; reflexivity. }
  destruct (gateway_ordered_pair_slices_native_uses backend process position (gateway_scoped_builders registry actions attributes)
    (genuine actions attributes) actions_view attributes_view resources ipc rows (RECORDING actions attributes HEADERS) pair_observation
    entry_arguments environment temporaries initial_memory initial_world allocated storage data control source_prefix
    (Callstate (gateway_spawn_signature gateway_posix_spawn_api) (gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment called_temps Kstop) memory) world data_identity control_identity
    ENTRY DATA_STORAGE CONTROL_STORAGE ORIGINS)
    as (data_use & control_use & data_position & control_position & data_prefix & control_prefix & data_memory & control_memory &
      data_world & control_world & data_event & control_event & DATA_INVOCATION & CONTROL_INVOCATION & DATA_KIND & CONTROL_KIND &
      DATA_POSITION & CONTROL_POSITION & DATA_ROW & CONTROL_ROW & DATA_PENDING & CONTROL_PENDING & DATA_BOUND & CONTROL_BOUND &
      DATA_LEFT_OBJECT & DATA_RIGHT_OBJECT & DATA_LEFT_DESCRIPTION & DATA_RIGHT_DESCRIPTION & CONTROL_LEFT_OBJECT & CONTROL_RIGHT_OBJECT &
      CONTROL_LEFT_DESCRIPTION & CONTROL_RIGHT_DESCRIPTION & DATA_CHECKED & CONTROL_CHECKED).
  assert (INVOCATION_KEY : NP.LeanCage_Host_ChannelCode_Invocation_key
    (gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world)) =
    gateway_native_shared_key {|gateway_source_process:=process initial_world;gateway_source_entry_position:=position initial_world;
        gateway_source_actions:=actions;gateway_source_attributes:=attributes|}).
  { unfold gateway_channel_invocation, gateway_native_shared_key; cbn.
    rewrite ACTIONS_STORAGE, ATTRIBUTES_STORAGE; reflexivity. }
  assert (CHANNELS : forall born birth_position birth_row child current selected row image,
    pending (gateway_spawn_call_values blocks symbols actions attributes) memory world born birth_position birth_row ->
    samples born birth_position = Some birth_row ->
    gateway_native_row_product birth_row = NP.LeanCage_Host_NativeCode_Product_created (Nat_of_nat child) ->
    executing (gateway_spawn_call_values blocks symbols actions attributes) memory world child current selected row ->
    samples current selected = Some row -> gateway_native_row_process row = Nat_of_nat child ->
    gateway_native_row_product row = NP.LeanCage_Host_NativeCode_Product_executed (Nat_of_nat image) ->
    exists birth execution,
      births born child = Some birth /\ births current child = Some birth /\ executed current child execution /\
      gateway_exec_from_birth birth execution /\ gateway_exec_image_object execution = image /\
      gateway_native_row_operation row = gateway_native_execution_code execution /\
      gateway_native_full_table_view (gateway_exec_descriptors execution) (gateway_native_row_output row) /\
      gateway_native_channels_checked (gateway_native_row_output row)
        (NP.LeanCage_Host_ChannelCode_PairUse_rightObject data_use)
        (NP.LeanCage_Host_ChannelCode_PairUse_rightObject control_use)).
  { intros born birth_position birth_row child current selected row image BIRTH_PENDING BIRTH_ROW CREATED EXECUTING ROW PROCESS IMAGE.
    rewrite DATA_RIGHT_OBJECT, CONTROL_RIGHT_OBJECT.
    eapply gateway_actual_source_pair_exec_channels with
      (actors := RECORDING actions attributes HEADERS) (primitive := PENDING actions attributes HEADERS)
      (snapshots := SNAPSHOTS actions attributes HEADERS)
      (key := {|gateway_source_process:=process initial_world;gateway_source_entry_position:=position initial_world;
        gateway_source_actions:=actions;gateway_source_attributes:=attributes|}) (code := (gateway_native_spawn_code engine_bytes[engine_bytes][spawn_path_bytes;spawn_locale_bytes]
        (exchange_sdk_plan data_right control_right)actual_attributes))
      (data_identity := data_identity) (control_identity := control_identity)
      (data_left := data_left) (data_right := data_right) (control_left := control_left) (control_right := control_right)
      (data := data) (control := control); try eassumption.
 }
  exists data, control, actions, attributes, blocks, symbols, data_identity, control_identity,
    data_left, data_right, control_left, control_right, source_prefix, suffix, memory, world, called_temps, actual_attributes,
    storage, data_use, control_use, data_position, control_position, data_prefix, control_prefix, data_memory, control_memory,
    data_world, control_world, data_event, control_event.
  repeat first [assumption | split].
Qed.
End NativeEntry.
