(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Pair-copyout source slices survive actual
   flags, scoped SDK setup and the selected original spawn frontier. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import
  GatewayBuilderDescriptors GatewayBuilderHistory GatewayBuilderScopes GatewayBuilderThreads GatewayCallerBuffers GatewayContexts
  GatewayDescriptorRoots GatewayExchangeBuilders GatewayExchangeConnections GatewayExchangeContext GatewayExchangeEntry GatewayExchangeFlagContext
  GatewayExchangeFlags GatewayExchangeInitialize GatewayExchangeInitialized GatewayExchangeLaunch GatewayExchangePairOrigins GatewayExchangePrepared
  GatewayExchangeSDK GatewayExchangeScope GatewayExchangeSetup GatewayExchangeStorage GatewayFramedRuntime GatewayLocalRuntime
  GatewayMachine GatewayNativeRoots GatewayOperations GatewayPairContext GatewayPairCopyout GatewayPairHistory
  GatewayPairOccurrence GatewayPairPosition GatewayPassiveResources GatewaySDKInputs GatewaySource GatewaySpawnABI
  GatewaySpawnActions GatewaySpawnCall GatewaySpawnDescriptors GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnVectorMemory
  GatewaySpawnVectorStores GatewayStreamInterface GatewayThreadRuntime GatewayVectorCells.
Import ListNotations.
Open Scope Z_scope.

Module PairOriginBuilders.
Section Builders.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option Values.val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop)
    (builders:World->gateway_spawn_builders)(genuine:mem->World->Prop)(footprint:World->block->Z->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (passive:gateway_passive_resource_runtime backend resources)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(actions attributes:block).
Context(history:gateway_builder_history_runtime backend native builders actions attributes).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state).
Local Definition rooted:=gateway_native_root_discipline native discipline[actions;attributes].
Local Definition retained snapshot:=gateway_builder_thread_discipline rooted builders snapshot.
Local Lemma rooted_headers mode memory world:
  rooted mode memory world->gateway_builder_headers native actions attributes memory world.
Proof. intros[SIDE ROOTS];exact ROOTS. Qed.
Local Definition rooted_thread:=gateway_thread_with_native_roots backend io native stable discipline thread_errno thread[actions;attributes].
Local Definition rooted_descriptors:=gateway_descriptors_with_native_roots backend io native stable discipline resources ipc
  descriptors[actions;attributes].
Local Definition retained_thread snapshot:=gateway_thread_with_builder_history backend io native stable rooted thread_errno
  rooted_thread builders actions attributes history rooted_headers snapshot.
Local Definition retained_descriptors snapshot:=gateway_descriptors_with_builder_history backend io native stable rooted resources ipc
  rooted_descriptors builders actions attributes history rooted_headers snapshot.
Local Definition context:=gateway_exchange_context native stable discipline resources readonly selected reference owner original.

Theorem actual_exchange_empty_sdk_before_initializers_distinct allocation_before allocated environment temporaries data control
    before world events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_pair=Some(data,tarray tint 2)->environment!_control=Some(control,tarray tint 2)->data<>control->
  selected data->selected control->(forall position,~readonly data position)->(forall position,~readonly control position)->
  Mem.range_perm reference data 0 8 Cur Freeable->Mem.range_perm reference control 0 8 Cur Freeable->
  gateway_builder_headers native actions attributes before world->
  gateway_builder_actions(builders world)=None->gateway_builder_attributes(builders world)=None->context before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists began flags prefix suffix sdk_before sdk_world(data_identity control_identity:gateway_pair_identity ipc)
    data_left data_right control_left control_right,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_setup_after 6)Kstop environment
        (exchange_flags_temps flags data_right(exchange_connections_temps began temporaries))sdk_before)sdk_world) /\
    gateway_copyout_pairs_slice_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world prefix
      (State f_host_exchange(exchange_setup_after 6)Kstop environment
        (exchange_flags_temps flags data_right(exchange_connections_temps began temporaries))sdk_before)sdk_world
      data_identity control_identity /\
    pair_right_object ipc data_identity<>pair_right_object ipc control_identity /\
    (4<=data_left)%Z /\(4<=data_right)%Z /\(4<=control_left)%Z /\(4<=control_right)%Z /\
    gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
      data control data_left data_right control_left control_right builders genuine None None sdk_before sdk_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 6)Kstop environment
        (exchange_flags_temps flags data_right(exchange_connections_temps began temporaries))sdk_before)sdk_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_READONLY CONTROL_READONLY
    DATA_RANGE CONTROL_RANGE HEADERS EMPTY_ACTIONS EMPTY_ATTRIBUTES INITIAL RUN.
  set(snapshot:=builders world).
  assert(STRONG:gateway_exchange_context native stable(retained snapshot)resources readonly selected reference owner original before world).
  { destruct INITIAL as[SIDE REST];split;[split;[split;assumption|reflexivity]|exact REST]. }
  destruct(PairOriginConnections.actual_exchange_connections_before_flags_distinct backend io native stable(retained snapshot)thread_errno
    resources ipc(retained_thread snapshot)(retained_descriptors snapshot)passive readonly selected reference owner original
    allocation_before allocated environment temporaries data control before world events arguments continuation after next
    ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_READONLY CONTROL_READONLY DATA_RANGE CONTROL_RANGE STRONG RUN)
    as(began&connection_prefix&flag_events&flag_before&flag_world&data_identity&control_identity&data_left&data_right&control_left&control_right&
      EVENTS1&CLOCK&CONNECTIONS&OBJECTS&DATA_LEFT&DATA_RIGHT&CONTROL_LEFT&CONTROL_RIGHT&
      DATA_CONTEXT&CONTROL_CONTEXT&FLAG_BASE&ORDER&FLAGS_RUN).
  assert(FLAGS:gateway_flag_context native stable(retained snapshot)resources ipc readonly selected reference owner original
    data_identity control_identity data control data_left data_right control_left control_right true true flag_before flag_world).
  { eapply gateway_flag_context_from_pairs;[exact DATA_CONTEXT|exact CONTROL_CONTEXT|exact FLAG_BASE]. }
  destruct(actual_exchange_flags_before_sdk backend io native stable(retained snapshot)thread_errno resources ipc
    (retained_thread snapshot)(retained_descriptors snapshot)readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right DATA_SELECTED CONTROL_SELECTED allocation_before allocated environment
    (exchange_connections_temps began temporaries)flag_before flag_world flag_events arguments continuation after next
    ALLOC DATA FLAGS FLAGS_RUN)
    as(flags&flag_prefix&suffix&sdk_before&sdk_world&NONNEGATIVE&EVENTS2&FLAG_PREFIX&SDK_READY&SUFFIX).
  destruct SDK_READY as[[[NORMAL ROOTS]SNAPSHOT]FLAG_REST].
  assert(ACT:gateway_builder_actions(builders sdk_world)=None)by(rewrite SNAPSHOT;exact EMPTY_ACTIONS).
  assert(ATTR:gateway_builder_attributes(builders sdk_world)=None)by(rewrite SNAPSHOT;exact EMPTY_ATTRIBUTES).
  exists began,flags,(connection_prefix++flag_prefix),suffix,sdk_before,sdk_world,data_identity,control_identity,
    data_left,data_right,control_left,control_right.
  split;[rewrite EVENTS1,EVENTS2,app_assoc;reflexivity|].
  split;[eapply gateway_steps_append;[exact CONNECTIONS|exact FLAG_PREFIX]|].
  split;[eapply gateway_copyout_pairs_slice_ordered_append;[exact ORDER|exact FLAG_PREFIX]|]. split;[exact OBJECTS|]. split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|].
  split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|]. split.
  - split;[split;[exact NORMAL|exact FLAG_REST]|].
    split;[eapply gateway_builder_empty;[exact sdk|exact ACT|exact ATTR]|]. split;assumption.
  - exact SUFFIX.
Qed.
End Builders.
End PairOriginBuilders.

Module PairOriginLaunch.
Section Launch.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option Values.val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop)
    (builders:World->gateway_spawn_builders)(genuine:mem->World->Prop)(footprint:World->block->Z->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (passive:gateway_passive_resource_runtime backend resources)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state)
    (data control actions attributes:block).
Context(history:gateway_builder_history_runtime backend native builders actions attributes)
    (initializers:gateway_spawn_initializer_runtime backend io native stable discipline resources builders genuine footprint actions attributes).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(ACTIONS_SELECTED:selected actions)
    (ATTRIBUTES_SELECTED:selected attributes)(DATA_CONTROL:data<>control)(ACTIONS_DATA:actions<>data)(ACTIONS_CONTROL:actions<>control)
    (ATTRIBUTES_DATA:attributes<>data)(ATTRIBUTES_CONTROL:attributes<>control)(HEADERS:actions<>attributes)
    (DATA_READONLY:forall position,~readonly data position)(CONTROL_READONLY:forall position,~readonly control position)
    (ACTIONS_READONLY:forall position,~readonly actions position)(ATTRIBUTES_READONLY:forall position,~readonly attributes position)
    (DATA_RANGE:Mem.range_perm reference data 0 8 Cur Freeable)(CONTROL_RANGE:Mem.range_perm reference control 0 8 Cur Freeable)
    (ACTIONS_RANGE:Mem.range_perm reference actions 0 80 Cur Freeable)
    (ATTRIBUTES_RANGE:Mem.range_perm reference attributes 0 336 Cur Freeable).
Variables(allocation_before allocated:mem)(environment:env).
Hypotheses(ALLOC:alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated)
    (ACTIONS:environment!_actions=Some(actions,gateway_actions_type))
    (ATTRIBUTES:environment!_attributes=Some(attributes,gateway_attributes_type))
    (DATA:environment!_pair=Some(data,tarray tint 2))(CONTROL:environment!_control=Some(control,tarray tint 2)).
Variables(blocks:gateway_spawn_vector_blocks)(symbols:gateway_spawn_vector_symbols).
Hypotheses(LOCATIONS:gateway_spawn_vector_locations(Clight.globalenv prog)environment blocks symbols)
    (DISTINCT:gateway_spawn_blocks_distinct blocks)
    (CELLS:forall cell,In cell(gateway_spawn_cell_plan blocks symbols)->
      selected(vector_cell_block cell) /\vector_cell_block cell<>data /\vector_cell_block cell<>control /\
      vector_cell_block cell<>actions /\vector_cell_block cell<>attributes /\
      (forall position,~readonly(vector_cell_block cell)position))
    (ACCESS:Forall(gateway_vector_writable reference)(gateway_spawn_cell_plan blocks symbols)).

Theorem actual_exchange_source_launch_distinct temporaries before world events arguments continuation after next:
  gateway_builder_headers native actions attributes before world->
  gateway_builder_actions(builders world)=None->gateway_builder_attributes(builders world)=None->
  gateway_exchange_context native stable discipline resources readonly selected reference owner original before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists began flags data_identity control_identity data_left data_right control_left control_right prefix suffix memory current,
    events=prefix++suffix /\
    gateway_copyout_pairs_slice_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world prefix
      (Callstate(gateway_spawn_signature gateway_posix_spawn_api)(gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment(exchange_launch_temps began flags data_right control_right temporaries)Kstop)memory)current
      data_identity control_identity /\
    pair_right_object ipc data_identity<>pair_right_object ipc control_identity /\
    4<=data_left /\4<=data_right /\4<=control_left /\4<=control_right /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
        (gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment(exchange_launch_temps began flags data_right control_right temporaries)Kstop)memory)current) /\
    gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
      data control data_left data_right control_left control_right builders genuine
      (Some(Vptr actions Ptrofs.zero,exchange_sdk_plan data_right control_right))
      (Some(Vptr attributes Ptrofs.zero,exchange_sdk_attributes))memory current /\
    Forall(gateway_vector_loaded memory)(gateway_spawn_cell_plan blocks symbols) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
        (gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment(exchange_launch_temps began flags data_right control_right temporaries)Kstop)memory)current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ROOTS EMPTY_ACTIONS EMPTY_ATTRIBUTES INITIAL RUN.
  destruct(PairOriginBuilders.actual_exchange_empty_sdk_before_initializers_distinct backend io native stable discipline thread_errno resources ipc builders genuine footprint
    thread descriptors passive sdk actions attributes history readonly selected reference owner original allocation_before allocated environment
    temporaries data control before world events arguments continuation after next ALLOC DATA CONTROL DATA_CONTROL DATA_SELECTED
    CONTROL_SELECTED DATA_READONLY CONTROL_READONLY DATA_RANGE CONTROL_RANGE ROOTS EMPTY_ACTIONS EMPTY_ATTRIBUTES INITIAL RUN)
    as(began&flags&connection_prefix&initialization&sdk_before&sdk_world&data_identity&control_identity&data_left&data_right&control_left&control_right&
      EVENTS1&CONNECTIONS&ORDER&OBJECTS&DATA_LEFT&DATA_RIGHT&CONTROL_LEFT&CONTROL_RIGHT&EMPTY_SDK&SDK_RUN).
  set(connection_temps:=exchange_flags_temps flags data_right(exchange_connections_temps began temporaries)).
  destruct(actual_exchange_initializers_before_group backend io native stable discipline thread_errno resources ipc builders genuine footprint
    thread descriptors sdk readonly selected reference owner original data_identity control_identity data control data_left data_right control_left
    control_right actions attributes initializers DATA_SELECTED CONTROL_SELECTED ACTIONS_SELECTED ATTRIBUTES_SELECTED ACTIONS_DATA ACTIONS_CONTROL
    ATTRIBUTES_DATA ATTRIBUTES_CONTROL HEADERS ACTIONS_READONLY ATTRIBUTES_READONLY ACTIONS_RANGE ATTRIBUTES_RANGE allocation_before allocated
    environment connection_temps sdk_before sdk_world initialization arguments continuation after next ALLOC ACTIONS ATTRIBUTES EMPTY_SDK SDK_RUN)
    as(initializer_prefix&edits&edit_before&edit_world&EVENTS2&INITIALIZERS&INITIALIZED&EDIT_RUN).
  set(initialized_temps:=exchange_initialized_temps connection_temps).
  destruct(actual_exchange_sdk_selected_call backend io native stable discipline thread_errno resources ipc builders genuine footprint
    thread descriptors sdk readonly selected reference owner original data_identity control_identity data control data_left data_right control_left
    control_right actions attributes DATA_SELECTED CONTROL_SELECTED ACTIONS_SELECTED ATTRIBUTES_SELECTED ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA
    ATTRIBUTES_CONTROL ACTIONS_READONLY ATTRIBUTES_READONLY ACTIONS_RANGE ATTRIBUTES_RANGE allocation_before allocated environment ALLOC ACTIONS
    ATTRIBUTES DATA CONTROL blocks symbols LOCATIONS DISTINCT CELLS ACCESS initialized_temps edit_before edit_world edits arguments continuation
    after next ltac:(apply PTree.gss)INITIALIZED EDIT_RUN)
    as(edit_prefix&suffix&memory&current&EVENTS3&EDITS&FINAL&LOADED&SUFFIX).
  exists began,flags,data_identity,control_identity,data_left,data_right,control_left,control_right,
    (connection_prefix++initializer_prefix++edit_prefix),suffix,memory,current.
  split;[rewrite EVENTS1,EVENTS2,EVENTS3;repeat rewrite app_assoc;reflexivity|].
  split;[eapply gateway_copyout_pairs_slice_ordered_append;[exact ORDER|eapply gateway_steps_append;[exact INITIALIZERS|exact EDITS]]|]. split;[exact OBJECTS|]. split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|].
  split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|]. split.
  - eapply gateway_steps_append;[exact CONNECTIONS|]. eapply gateway_steps_append;[exact INITIALIZERS|exact EDITS].
  - split;[exact FINAL|]. split;[exact LOADED|exact SUFFIX].
Qed.
End Launch.
End PairOriginLaunch.

Module PairOriginPrepared.
Record gateway_exchange_spawn_frontier {World Event}(backend:gateway_backend World Event)
    (native:World->block->Prop)(stable:World->block->Z->Prop)discipline resources ipc builders genuine
    readonly reference owner environment temporaries data control actions attributes blocks symbols before world events
    target_arguments target_continuation target_memory target_world:Type:={
  exchange_frontier_began:Values.val;
  exchange_frontier_flags:int;
  exchange_frontier_data_identity:gateway_pair_identity ipc;
  exchange_frontier_control_identity:gateway_pair_identity ipc;
  exchange_frontier_data_left:Z;
  exchange_frontier_data_right:Z;
  exchange_frontier_control_left:Z;
  exchange_frontier_control_right:Z;
  exchange_frontier_prefix:list(gateway_event Event);
  exchange_frontier_suffix:list(gateway_event Event);
  exchange_frontier_memory:mem;
  exchange_frontier_world:World;
  exchange_frontier_events:events=exchange_frontier_prefix++exchange_frontier_suffix;
  exchange_frontier_pair_order:gateway_copyout_pairs_slice_ordered backend resources ipc data control
    (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world exchange_frontier_prefix
    (Callstate(gateway_spawn_signature gateway_posix_spawn_api)(gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment(exchange_launch_temps exchange_frontier_began exchange_frontier_flags
        exchange_frontier_data_right exchange_frontier_control_right temporaries)Kstop)exchange_frontier_memory)exchange_frontier_world
    exchange_frontier_data_identity exchange_frontier_control_identity;
  exchange_frontier_endpoints_separate:pair_right_object ipc exchange_frontier_data_identity<>
    pair_right_object ipc exchange_frontier_control_identity;
  exchange_frontier_data_left_bound:4<=exchange_frontier_data_left;
  exchange_frontier_data_right_bound:4<=exchange_frontier_data_right;
  exchange_frontier_control_left_bound:4<=exchange_frontier_control_left;
  exchange_frontier_control_right_bound:4<=exchange_frontier_control_right;
  exchange_frontier_source:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)exchange_frontier_prefix
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
      (gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment(exchange_launch_temps exchange_frontier_began exchange_frontier_flags
        exchange_frontier_data_right exchange_frontier_control_right temporaries)Kstop)exchange_frontier_memory)exchange_frontier_world);
  exchange_frontier_context:gateway_sdk_context native stable discipline resources ipc readonly(exchange_selected_block environment)
    reference owner(resources owner)exchange_frontier_data_identity exchange_frontier_control_identity data control
    exchange_frontier_data_left exchange_frontier_data_right exchange_frontier_control_left exchange_frontier_control_right builders genuine
    (Some(Vptr actions Ptrofs.zero,exchange_sdk_plan exchange_frontier_data_right exchange_frontier_control_right))
    (Some(Vptr attributes Ptrofs.zero,exchange_sdk_attributes))exchange_frontier_memory exchange_frontier_world;
  exchange_frontier_vectors:Forall(gateway_vector_loaded exchange_frontier_memory)(gateway_spawn_cell_plan blocks symbols);
  exchange_frontier_tail:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
      (gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment(exchange_launch_temps exchange_frontier_began exchange_frontier_flags
        exchange_frontier_data_right exchange_frontier_control_right temporaries)Kstop)exchange_frontier_memory)exchange_frontier_world)
    exchange_frontier_suffix
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)target_arguments target_continuation target_memory)target_world)
}.

End PairOriginPrepared.

Module PairOriginEntry.
Record gateway_exchange_entry_frontier {World Event}(backend:gateway_backend World Event)
    (native:World->block->Prop)(stable:World->block->Z->Prop)discipline resources ipc builders genuine
    readonly reference owner environment temporaries data control actions attributes blocks symbols before world events
    target_arguments target_continuation target_memory target_world:Type:={
  exchange_entry_loaded:Values.val;
  exchange_entry_prefix:list(gateway_event Event);
  exchange_entry_body_events:list(gateway_event Event);
  exchange_entry_memory:mem;
  exchange_entry_world:World;
  exchange_entry_events:events=exchange_entry_prefix++exchange_entry_body_events;
  exchange_entry_quiet:Forall GatewayReadonly.gateway_quiet_event exchange_entry_prefix;
  exchange_entry_source:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries before)world)
    exchange_entry_prefix(gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment
      (exchange_entry_temps exchange_entry_loaded temporaries)exchange_entry_memory)exchange_entry_world);
  exchange_entry_body:PairOriginPrepared.gateway_exchange_spawn_frontier backend native stable discipline resources ipc builders genuine
    readonly reference owner environment(exchange_entry_temps exchange_entry_loaded temporaries)data control actions attributes blocks symbols
    exchange_entry_memory exchange_entry_world exchange_entry_body_events target_arguments target_continuation target_memory target_world
}.

Section EntryPrepared.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option Values.val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop)
    (registry:World->gateway_builder_registry)(genuine:block->block->mem->World->Prop)
    (footprint:block->block->World->block->Z->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (passive:gateway_passive_resource_runtime backend resources).
(* The primitive families are instantiated only at the distinct actual source
   header lifetimes selected below. They assert no exchange/helper outcome. *)
Hypothesis SDK:forall actions attributes,actions<>attributes->gateway_spawn_builder_runtime backend io native stable discipline resources
  (gateway_scoped_builders registry actions attributes)(genuine actions attributes)(footprint actions attributes).
Hypothesis HISTORY:forall actions attributes,actions<>attributes->gateway_builder_history_runtime backend native
  (gateway_scoped_builders registry actions attributes)actions attributes.
Hypothesis INITIALIZERS:forall actions attributes,actions<>attributes->gateway_spawn_initializer_runtime backend io native stable discipline resources
  (gateway_scoped_builders registry actions attributes)(genuine actions attributes)(footprint actions attributes)actions attributes.

Theorem actual_exchange_allocated_entry_spawn allocation_before allocated environment temporaries world readonly events
    target_arguments target_continuation target_memory target_world:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  discipline None allocated world->gateway_native_environment native world allocated environment->
  gateway_caller_readonly native stable readonly allocation_before world->gateway_resource_valid(resources world)->
  gateway_builder_registry_allocated allocation_before(registry world)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries allocated)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)target_arguments target_continuation target_memory)target_world)->
  exists data control actions attributes blocks symbols,
    gateway_exchange_storage native stable readonly allocated world environment data control actions attributes blocks symbols /\
    inhabited(gateway_exchange_entry_frontier backend native stable discipline resources ipc
      (gateway_scoped_builders registry actions attributes)(genuine actions attributes)readonly allocated world environment temporaries
      data control actions attributes blocks symbols allocated world events target_arguments target_continuation target_memory target_world).
Proof.
  intros ALLOC SIDE NATIVE READONLY VALID REGISTRY RUN.
  destruct(actual_exchange_storage_inputs native stable allocation_before allocated environment world readonly ALLOC NATIVE READONLY)
    as(data&control&actions&attributes&blocks&symbols&STORAGE).
  pose proof STORAGE as STORAGE_COPY.
  destruct STORAGE_COPY as[DATA CONTROL ACTIONS ATTRIBUTES DATA_CONTROL ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA ATTRIBUTES_CONTROL
    HEADERS DATA_READONLY CONTROL_READONLY ACTIONS_READONLY ATTRIBUTES_READONLY DATA_RANGE CONTROL_RANGE ACTIONS_RANGE ATTRIBUTES_RANGE
    LOCATIONS DISTINCT CELLS ACCESS FAMILY ROOTS].
  destruct(gateway_fresh_builder_scope_empty registry world allocation_before actions attributes REGISTRY
    ltac:(eapply actual_exchange_allocated_local_fresh with(identifier:=_actions)(ty:=gateway_actions_type);
      [exact ALLOC|cbn;auto 14|exact ACTIONS])
    ltac:(eapply actual_exchange_allocated_local_fresh with(identifier:=_attributes)(ty:=gateway_attributes_type);
      [exact ALLOC|cbn;auto 14|exact ATTRIBUTES]))as[EMPTY_ACTIONS EMPTY_ATTRIBUTES].
  assert(INITIAL:gateway_exchange_context native stable discipline resources readonly(exchange_selected_block environment)
    allocated world(resources world)allocated world).
  { split;[exact SIDE|]. split;[split;[exact VALID|apply gateway_resource_reference_refl]|exact FAMILY]. }
  assert(SELECTED_DATA:exchange_selected_block environment data)by(exists _pair,(tarray tint 2);exact DATA).
  assert(SELECTED_CONTROL:exchange_selected_block environment control)by(exists _control,(tarray tint 2);exact CONTROL).
  assert(SELECTED_ACTIONS:exchange_selected_block environment actions)by(exists _actions,gateway_actions_type;exact ACTIONS).
  assert(SELECTED_ATTRIBUTES:exchange_selected_block environment attributes)by(exists _attributes,gateway_attributes_type;exact ATTRIBUTES).
  set(builders:=gateway_scoped_builders registry actions attributes).
  set(property:=fun memory current=>
    gateway_exchange_context native stable discipline resources readonly(exchange_selected_block environment)
      allocated world(resources world)memory current /\
    gateway_builder_actions(builders current)=None /\gateway_builder_attributes(builders current)=None).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros before current changed future[BASE[ACT ATTR]]AMBIENT.
    assert(HEADERS_READY:gateway_builder_headers native actions attributes before current).
    { intros object MEMBER;cbn in MEMBER;destruct MEMBER as[SAME|[SAME|FALSE]];try contradiction;subst object.
      - exact(conj(proj1((proj2(proj2 BASE))actions SELECTED_ACTIONS))
          (proj1(proj2((proj2(proj2 BASE))actions SELECTED_ACTIONS)))).
      - exact(conj(proj1((proj2(proj2 BASE))attributes SELECTED_ATTRIBUTES))
          (proj1(proj2((proj2(proj2 BASE))attributes SELECTED_ATTRIBUTES)))). }
    pose proof(gateway_builder_history_ambient backend native builders actions attributes(HISTORY actions attributes HEADERS)
      before current changed future HEADERS_READY AMBIENT)as SNAPSHOT.
    split.
    - eapply gateway_exchange_context_ambient;[exact thread|exact descriptors|exact BASE|exact AMBIENT].
    - rewrite SNAPSHOT;split;assumption. }
  assert(GUARD_INITIAL:property allocated world)by(split;[exact INITIAL|split;assumption]).
  destruct(actual_exchange_initialized_cut backend property CLOSED environment temporaries allocation_before allocated
    allocated world events target_arguments target_continuation target_memory target_world ALLOC GUARD_INITIAL RUN)
    as(guard_prefix & body_events & guarded & guarded_world & guard_value & EVENTS_GUARD & QUIET & GUARD_PREFIX &
      [GUARDED[ACT ATTR]] & GUARDED_RUN).
  assert(GUARDED_ROOTS:gateway_builder_headers native actions attributes guarded guarded_world).
  { intros object MEMBER;cbn in MEMBER;destruct MEMBER as[SAME|[SAME|FALSE]];try contradiction;subst object.
    - exact(conj(proj1((proj2(proj2 GUARDED))actions SELECTED_ACTIONS))
        (proj1(proj2((proj2(proj2 GUARDED))actions SELECTED_ACTIONS)))).
    - exact(conj(proj1((proj2(proj2 GUARDED))attributes SELECTED_ATTRIBUTES))
        (proj1(proj2((proj2(proj2 GUARDED))attributes SELECTED_ATTRIBUTES)))). }
  destruct(PairOriginLaunch.actual_exchange_source_launch_distinct backend io native stable discipline thread_errno resources ipc
    (gateway_scoped_builders registry actions attributes)(genuine actions attributes)(footprint actions attributes)
    thread descriptors passive(SDK actions attributes HEADERS)readonly(exchange_selected_block environment)allocated world(resources world)
    data control actions attributes(HISTORY actions attributes HEADERS)(INITIALIZERS actions attributes HEADERS)
    SELECTED_DATA SELECTED_CONTROL SELECTED_ACTIONS SELECTED_ATTRIBUTES DATA_CONTROL ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA
    ATTRIBUTES_CONTROL HEADERS DATA_READONLY CONTROL_READONLY ACTIONS_READONLY ATTRIBUTES_READONLY DATA_RANGE CONTROL_RANGE
    ACTIONS_RANGE ATTRIBUTES_RANGE allocation_before allocated environment ALLOC ACTIONS ATTRIBUTES DATA CONTROL blocks symbols
    LOCATIONS DISTINCT CELLS ACCESS (exchange_entry_temps guard_value temporaries)guarded guarded_world body_events target_arguments target_continuation target_memory target_world
    GUARDED_ROOTS ACT ATTR GUARDED GUARDED_RUN)
    as(began&flags&data_identity&control_identity&data_left&data_right&control_left&control_right&prefix&suffix&memory&current&
      EVENTS&ORDER&OBJECTS&DATA_LEFT&DATA_RIGHT&CONTROL_LEFT&CONTROL_RIGHT&PREFIX&CONTEXT&VECTORS&TAIL).
  exists data,control,actions,attributes,blocks,symbols;split;[exact STORAGE|]. constructor.
  refine({|exchange_entry_loaded:=guard_value;exchange_entry_prefix:=guard_prefix;exchange_entry_body_events:=body_events;
    exchange_entry_memory:=guarded;exchange_entry_world:=guarded_world;exchange_entry_events:=EVENTS_GUARD;
    exchange_entry_quiet:=QUIET;exchange_entry_source:=GUARD_PREFIX|}).
  refine({|PairOriginPrepared.exchange_frontier_began:=began;PairOriginPrepared.exchange_frontier_flags:=flags;PairOriginPrepared.exchange_frontier_data_identity:=data_identity;
    PairOriginPrepared.exchange_frontier_control_identity:=control_identity;PairOriginPrepared.exchange_frontier_data_left:=data_left;PairOriginPrepared.exchange_frontier_data_right:=data_right;
    PairOriginPrepared.exchange_frontier_control_left:=control_left;PairOriginPrepared.exchange_frontier_control_right:=control_right;PairOriginPrepared.exchange_frontier_prefix:=prefix;
    PairOriginPrepared.exchange_frontier_suffix:=suffix;PairOriginPrepared.exchange_frontier_memory:=memory;PairOriginPrepared.exchange_frontier_world:=current|});assumption.
Qed.
End EntryPrepared.

End PairOriginEntry.
