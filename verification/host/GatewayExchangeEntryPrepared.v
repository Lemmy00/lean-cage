(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual initialization guard precedes scoped SDK setup and the real spawn
   frontier. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewaySpawnActions GatewaySpawnDescriptors GatewayPassiveResources
  GatewayBuilderHistory GatewayBuilderScopes GatewayPairContext GatewayPairPosition GatewayPairHistory GatewayExchangeSetup
  GatewayExchangeContext GatewayExchangeLaunch GatewayExchangeSDK GatewayExchangeEntry GatewayExchangeScope GatewayExchangeStorage
  GatewayLocalRuntime GatewayCallerBuffers GatewaySDKInputs GatewaySpawnVectorMemory GatewaySpawnVectorStores GatewayVectorCells
  GatewaySpawnCall GatewayContexts GatewayExchangePrepared GatewayExchangeInitialized GatewayFramedRuntime GatewayOperations.
Import ListNotations.
Open Scope Z_scope.

Record gateway_exchange_entry_frontier {World Event}(backend:gateway_backend World Event)
    (native:World->block->Prop)(stable:World->block->Z->Prop)discipline resources ipc builders genuine
    readonly reference owner environment temporaries data control actions attributes blocks symbols before world events
    target_arguments target_continuation target_memory target_world:Type:={
  exchange_entry_loaded:val;
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
  exchange_entry_body:gateway_exchange_spawn_frontier backend native stable discipline resources ipc builders genuine
    readonly reference owner environment(exchange_entry_temps exchange_entry_loaded temporaries)data control actions attributes blocks symbols
    exchange_entry_memory exchange_entry_world exchange_entry_body_events target_arguments target_continuation target_memory target_world
}.

Section EntryPrepared.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
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
  destruct(actual_exchange_source_launch_distinct backend io native stable discipline thread_errno resources ipc
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
  refine({|exchange_frontier_began:=began;exchange_frontier_flags:=flags;exchange_frontier_data_identity:=data_identity;
    exchange_frontier_control_identity:=control_identity;exchange_frontier_data_left:=data_left;exchange_frontier_data_right:=data_right;
    exchange_frontier_control_left:=control_left;exchange_frontier_control_right:=control_right;exchange_frontier_prefix:=prefix;
    exchange_frontier_suffix:=suffix;exchange_frontier_memory:=memory;exchange_frontier_world:=current|});assumption.
Qed.
End EntryPrepared.
