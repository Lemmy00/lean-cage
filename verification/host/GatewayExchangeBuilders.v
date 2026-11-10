(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Fresh scoped SDK headers stay empty through real clock and pair
   setup. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewaySpawnActions GatewayPassiveResources
  GatewayNativeRoots GatewayDescriptorRoots GatewayBuilderHistory GatewayBuilderThreads GatewayBuilderDescriptors
  GatewayPairContext GatewayPairOccurrence GatewayPairPosition GatewayExchangeSetup GatewayExchangeContext
  GatewayExchangeConnections GatewayExchangeFlagContext GatewayExchangeFlags GatewaySDKInputs GatewayContexts.
Import ListNotations.

Section Builders.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
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
    gateway_source_pairs_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity control_identity /\
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
  destruct(actual_exchange_connections_before_flags_distinct backend io native stable(retained snapshot)thread_errno
    resources ipc(retained_thread snapshot)(retained_descriptors snapshot)passive readonly selected reference owner original
    allocation_before allocated environment temporaries data control before world events arguments continuation after next
    ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_READONLY CONTROL_READONLY DATA_RANGE CONTROL_RANGE STRONG RUN)
    as(began&connection_prefix&flag_events&flag_before&flag_world&data_identity&control_identity&data_left&data_right&control_left&control_right&
      EVENTS1&CLOCK&CONNECTIONS&DATA_BIRTH&CONTROL_BIRTH&OBJECTS&DATA_LEFT&DATA_RIGHT&CONTROL_LEFT&CONTROL_RIGHT&
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
  split;[exact ORDER|]. split;[exact OBJECTS|]. split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|].
  split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|]. split.
  - split;[split;[exact NORMAL|exact FLAG_REST]|].
    split;[eapply gateway_builder_empty;[exact sdk|exact ACT|exact ATTR]|]. split;assumption.
  - exact SUFFIX.
Qed.
Theorem actual_exchange_empty_sdk_before_initializers allocation_before allocated environment temporaries data control
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
    gateway_source_pairs_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity control_identity /\
    (4<=data_left)%Z /\(4<=data_right)%Z /\(4<=control_left)%Z /\(4<=control_right)%Z /\
    gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
      data control data_left data_right control_left control_right builders genuine None None sdk_before sdk_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 6)Kstop environment
        (exchange_flags_temps flags data_right(exchange_connections_temps began temporaries))sdk_before)sdk_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_READONLY CONTROL_READONLY
    DATA_RANGE CONTROL_RANGE ROOTS EMPTY_ACTIONS EMPTY_ATTRIBUTES INITIAL RUN.
  destruct(actual_exchange_empty_sdk_before_initializers_distinct allocation_before allocated environment temporaries data control
    before world events arguments continuation after next ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_READONLY
    CONTROL_READONLY DATA_RANGE CONTROL_RANGE ROOTS EMPTY_ACTIONS EMPTY_ATTRIBUTES INITIAL RUN)
    as(began&flags&prefix&suffix&sdk_before&sdk_world&data_identity&control_identity&data_left&data_right&control_left&control_right&
      EVENTS&PREFIX&ORDER&OBJECTS&DATA_LEFT&DATA_RIGHT&CONTROL_LEFT&CONTROL_RIGHT&CONTEXT&SUFFIX).
  exists began,flags,prefix,suffix,sdk_before,sdk_world,data_identity,control_identity,data_left,data_right,control_left,control_right.
  split;[exact EVENTS|]. split;[exact PREFIX|]. split;[exact ORDER|]. split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|].
  split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|]. split;assumption.
Qed.

End Builders.
