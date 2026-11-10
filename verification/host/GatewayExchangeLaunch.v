(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One actual exchange creates its IPC and constructs its exact
   selected spawn. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewaySpawnActions GatewaySpawnDescriptors GatewayPassiveResources
  GatewayBuilderHistory GatewayPairContext GatewayPairPosition GatewayExchangeSetup GatewayExchangeContext
  GatewayExchangeBuilders GatewayExchangeFlags GatewayExchangeConnections GatewayExchangeInitialize GatewayExchangeSDK
  GatewaySDKInputs GatewaySpawnVectorMemory GatewaySpawnVectorStores GatewayVectorCells GatewaySpawnCall GatewayContexts.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_launch_temps began flags data_right control_right temporaries:=
  exchange_sdk_temps_exact data_right control_right(exchange_initialized_temps
    (exchange_flags_temps flags data_right(exchange_connections_temps began temporaries))).

Section Launch.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
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
    gateway_source_pairs_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity control_identity /\
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
  destruct(actual_exchange_empty_sdk_before_initializers_distinct backend io native stable discipline thread_errno resources ipc builders genuine footprint
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
  split;[exact ORDER|]. split;[exact OBJECTS|]. split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|].
  split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|]. split.
  - eapply gateway_steps_append;[exact CONNECTIONS|]. eapply gateway_steps_append;[exact INITIALIZERS|exact EDITS].
  - split;[exact FINAL|]. split;[exact LOADED|exact SUFFIX].
Qed.
Theorem actual_exchange_source_launch temporaries before world events arguments continuation after next:
  gateway_builder_headers native actions attributes before world->
  gateway_builder_actions(builders world)=None->gateway_builder_attributes(builders world)=None->
  gateway_exchange_context native stable discipline resources readonly selected reference owner original before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists began flags data_identity control_identity data_left data_right control_left control_right prefix suffix memory current,
    events=prefix++suffix /\
    gateway_source_pairs_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity control_identity /\
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
  destruct(actual_exchange_source_launch_distinct temporaries before world events arguments continuation after next
    ROOTS EMPTY_ACTIONS EMPTY_ATTRIBUTES INITIAL RUN)
    as(began&flags&data_identity&control_identity&data_left&data_right&control_left&control_right&prefix&suffix&memory&current&
      EVENTS&ORDER&OBJECTS&DATA_LEFT&DATA_RIGHT&CONTROL_LEFT&CONTROL_RIGHT&PREFIX&CONTEXT&VECTORS&TAIL).
  exists began,flags,data_identity,control_identity,data_left,data_right,control_left,control_right,prefix,suffix,memory,current.
  split;[exact EVENTS|]. split;[exact ORDER|]. split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|].
  split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|]. split;[exact PREFIX|]. split;[exact CONTEXT|]. split;assumption.
Qed.

End Launch.
