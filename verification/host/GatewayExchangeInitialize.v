(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real initializer guards precede the same exchange's group setup. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewaySpawnActions GatewaySpawnDescriptors
  GatewayPairContext GatewaySDKInputs GatewaySDKInitialize GatewaySDKRuntimeContext GatewaySDKInitializeSource
  GatewayExchangeSetup GatewayFramedRuntime GatewayLaunchPaths GatewayLaunchMemory GatewayLaunchSDK.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_initialized_temps temporaries:=
  sdk_initializer_temps gateway_initialize_attributes Int.zero
    (sdk_initializer_temps gateway_initialize_actions Int.zero temporaries).

Section Initialize.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop)
    (builders:World->gateway_spawn_builders)(genuine:mem->World->Prop)(footprint:World->block->Z->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)
    (original:gateway_resource_state)(data_identity control_identity:gateway_pair_identity ipc)
    (data control:block)(data_left data_right control_left control_right:Z)(actions attributes:block).
Context(initializers:gateway_spawn_initializer_runtime backend io native stable discipline resources
    builders genuine footprint actions attributes).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(ACTIONS_SELECTED:selected actions)
    (ATTRIBUTES_SELECTED:selected attributes)(ACTIONS_DATA:actions<>data)(ACTIONS_CONTROL:actions<>control)
    (ATTRIBUTES_DATA:attributes<>data)(ATTRIBUTES_CONTROL:attributes<>control)(HEADERS_SEPARATE:actions<>attributes)
    (ACTIONS_READONLY:forall position,~readonly actions position)
    (ATTRIBUTES_READONLY:forall position,~readonly attributes position)
    (ACTIONS_RANGE:Mem.range_perm reference actions 0 80 Cur Freeable)
    (ATTRIBUTES_RANGE:Mem.range_perm reference attributes 0 336 Cur Freeable).
Local Definition context:=gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original
  data_identity control_identity data control data_left data_right control_left control_right builders genuine.
Local Definition action_state:option(val*list gateway_spawn_action):=Some(Vptr actions Ptrofs.zero,[]).
Local Definition attribute_state:=Some(Vptr attributes Ptrofs.zero,gateway_default_attributes).

Local Lemma context_closed act attr:gateway_ambient_closed backend(context act attr).
Proof.
  eapply gateway_sdk_context_ambient with(io:=io)(thread_errno:=thread_errno);
    eassumption.
Qed.

Theorem actual_exchange_initializers_before_group allocation_before allocated environment temporaries before world events
    arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_actions=Some(actions,gateway_actions_type)->
  environment!_attributes=Some(attributes,gateway_attributes_type)->
  context None None before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 6)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists prefix suffix initialized current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 6)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_setup_after 10)Kstop environment
        (exchange_initialized_temps temporaries)initialized)current) /\
    context action_state attribute_state initialized current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 10)Kstop environment
        (exchange_initialized_temps temporaries)initialized)current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC ACTIONS ATTRIBUTES INITIAL RUN.
  set(target:=fun(source:Clight.state)(current:World)=>exists memory,
    source=State f_host_exchange(exchange_setup_after 10)Kstop environment
      (exchange_initialized_temps temporaries)memory /\context action_state attribute_state memory current).
  assert(ATTR_PATH:forall memory,gateway_launch_path backend target(context action_state None)
    (State f_host_exchange(exchange_setup_after 8)Kstop environment
      (sdk_initializer_temps gateway_initialize_actions Int.zero temporaries)memory)).
  { intro memory.
    eapply gateway_launch_after_memory_prefix.
    - eapply actual_sdk_initializer_prefix with(initializer:=gateway_initialize_attributes);
        [apply context_closed|exact ALLOC|exact ATTRIBUTES].
    - eapply gateway_launch_sdk_operation;[discriminate|apply context_closed|].
      intros called current result changed later observed READY OPERATION.
      destruct(actual_sdk_attributes_initialize backend io native stable discipline resources ipc builders genuine footprint sdk
        readonly selected reference owner original data_identity control_identity data control data_left data_right
        control_left control_right actions attributes initializers DATA_SELECTED CONTROL_SELECTED ATTRIBUTES_SELECTED
        ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA ATTRIBUTES_CONTROL HEADERS_SEPARATE
        ATTRIBUTES_READONLY ATTRIBUTES_RANGE called current result changed later observed
        READY OPERATION)as[status[RESULT[IO POST]]].
      subst result;exists(context action_state
        (if Int.eq status Int.zero then attribute_state else None));split;[exact POST|].
      eapply actual_sdk_initializer_return_path with(initializer:=gateway_initialize_attributes);
        [apply context_closed|exact ALLOC|].
      intro ZERO;subst status;apply gateway_launch_reached;intros final final_world FINAL.
      exists final;split;[reflexivity|exact FINAL]. }
  assert(ACT_PATH:gateway_launch_path backend target(context None None)
    (State f_host_exchange(exchange_setup_after 6)Kstop environment temporaries before)).
  { eapply gateway_launch_after_memory_prefix.
    - eapply actual_sdk_initializer_prefix with(initializer:=gateway_initialize_actions);
        [apply context_closed|exact ALLOC|exact ACTIONS].
    - eapply gateway_launch_sdk_operation;[discriminate|apply context_closed|].
      intros called current result changed later observed READY OPERATION.
      destruct(actual_sdk_actions_initialize backend io native stable discipline resources ipc builders genuine footprint sdk
        readonly selected reference owner original data_identity control_identity data control data_left data_right
        control_left control_right actions attributes initializers DATA_SELECTED CONTROL_SELECTED ACTIONS_SELECTED
        ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA ATTRIBUTES_CONTROL HEADERS_SEPARATE
        ACTIONS_READONLY ACTIONS_RANGE called current result changed later observed
        READY OPERATION)as[status[RESULT[IO POST]]].
      subst result;exists(context(if Int.eq status Int.zero then action_state else None)None);split;[exact POST|].
      eapply actual_sdk_initializer_return_path with(initializer:=gateway_initialize_actions);
        [apply context_closed|exact ALLOC|].
      intro ZERO;subst status;apply ATTR_PATH. }
  destruct(gateway_launch_prefix_cut backend target(context None None)
    (State f_host_exchange(exchange_setup_after 6)Kstop environment temporaries before)before world events
    arguments continuation after next ACT_PATH INITIAL RUN)
    as(prefix&suffix&point&current&EVENTS&PREFIX&POINT&SUFFIX).
  destruct POINT as[initialized[SOURCE FINAL]];subst point.
  exists prefix,suffix,initialized,current;split;[exact EVENTS|]. split;[exact PREFIX|]. split;assumption.
Qed.
End Initialize.
