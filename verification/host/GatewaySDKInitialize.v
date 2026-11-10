(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual real SDK initializers produce the same caller's shadow. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI GatewaySpawnRuntime
  GatewaySpawnResources GatewaySpawnActions GatewaySpawnDescriptors GatewayPairContext GatewayCallerFamily GatewayExchangeFlagContext
  GatewaySDKInputs GatewaySDKPost.
Import ListNotations.
Open Scope Z_scope.

Section Initializers.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (resources:World->gateway_resource_state)(ipc:nat->Prop)(builders:World->gateway_spawn_builders)
    (genuine:mem->World->Prop)(footprint:World->block->Z->Prop).
Context(sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state)
    (data_identity control_identity:gateway_pair_identity ipc)(data control:block)(data_left data_right control_left control_right:Z)
    (actions attributes:block).
Context(initializers:gateway_spawn_initializer_runtime backend io native stable discipline resources builders genuine footprint actions attributes).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(ACTIONS_SELECTED:selected actions)(ATTRIBUTES_SELECTED:selected attributes)
    (ACTIONS_DATA:actions<>data)(ACTIONS_CONTROL:actions<>control)(ATTRIBUTES_DATA:attributes<>data)(ATTRIBUTES_CONTROL:attributes<>control)
    (HEADERS_SEPARATE:actions<>attributes)(ACTIONS_READONLY:forall position,~readonly actions position)
    (ATTRIBUTES_READONLY:forall position,~readonly attributes position)
    (ACTIONS_RANGE:Mem.range_perm reference actions 0 80 Cur Freeable)
    (ATTRIBUTES_RANGE:Mem.range_perm reference attributes 0 336 Cur Freeable).
Local Definition context:=gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original
  data_identity control_identity data control data_left data_right control_left control_right builders genuine.

Theorem actual_sdk_actions_initialize before world result after next observed:
  context None None before world->
  gateway_spawn_operation backend gateway_actions_init_api[Vptr actions Ptrofs.zero]before world result after next observed->
  exists status,result=Vint status /\io observed=None /\
    context(if Int.eq status Int.zero then Some(Vptr actions Ptrofs.zero,[])else None)None after next.
Proof.
  intros INITIAL OPERATION.
  destruct INITIAL as[FLAGS[GENUINE[ACT ATTR]]].
  pose proof(proj1 FLAGS)as SIDE;pose proof(proj1(proj2(proj2 FLAGS)))as VALID.
  destruct(gateway_sdk_header_from_family native stable readonly selected reference owner before world actions 80
    (proj1(proj2 FLAGS))ACTIONS_SELECTED ACTIONS_RANGE ltac:(change(0<=80<=18446744073709551616);lia))
    as[NATIVE POINTER].
  assert(ABSENT:forall position,~footprint world actions position).
  { intros position HERE.
    destruct(gateway_builder_native_footprint _ _ _ _ _ _ _ _ _ sdk before world actions position GENUINE NATIVE HERE)
      as[[offset[plan SOME]]|[offset[settings SOME]]];[rewrite ACT in SOME|rewrite ATTR in SOME];discriminate. }
  destruct(gateway_actions_initialize _ _ _ _ _ _ _ _ _ _ _ initializers before world result after next observed
    SIDE GENUINE VALID ACT NATIVE POINTER ABSENT OPERATION)as[POST[status[RESULT BUILDERS]]].
  pose proof POST as POST_COPY;destruct POST_COPY as(NORMAL&AFTER_GENUINE&AFTER_VALID&ACCESS&PERMISSIONS&MEMORY&FRAME&STATUS&EXCLUSIVE&IO).
  exists status;split;[exact RESULT|]. split;[exact IO|].
  eapply gateway_sdk_post_context with(actions:=None)(attributes:=None)(before:=before)(world:=world);
    [exact DATA_SELECTED|exact CONTROL_SELECTED|exact ACTIONS_DATA|exact ACTIONS_CONTROL|exact ACTIONS_READONLY|
      exact(conj FLAGS(conj GENUINE(conj ACT ATTR)))|exact POST| |].
  - rewrite BUILDERS;reflexivity.
  - rewrite BUILDERS;exact ATTR.
Qed.

Theorem actual_sdk_attributes_initialize before world result after next observed:
  context(Some(Vptr actions Ptrofs.zero,[]))None before world->
  gateway_spawn_operation backend gateway_attributes_init_api[Vptr attributes Ptrofs.zero]before world result after next observed->
  exists status,result=Vint status /\io observed=None /\
    context(Some(Vptr actions Ptrofs.zero,[]))
      (if Int.eq status Int.zero then Some(Vptr attributes Ptrofs.zero,gateway_default_attributes)else None)after next.
Proof.
  intros INITIAL OPERATION.
  destruct INITIAL as[FLAGS[GENUINE[ACT ATTR]]].
  pose proof(proj1 FLAGS)as SIDE;pose proof(proj1(proj2(proj2 FLAGS)))as VALID.
  destruct(gateway_sdk_header_from_family native stable readonly selected reference owner before world attributes 336
    (proj1(proj2 FLAGS))ATTRIBUTES_SELECTED ATTRIBUTES_RANGE ltac:(change(0<=336<=18446744073709551616);lia))
    as[NATIVE POINTER].
  assert(ABSENT:forall position,~footprint world attributes position).
  { intros position HERE.
    destruct(gateway_builder_native_footprint _ _ _ _ _ _ _ _ _ sdk before world attributes position GENUINE NATIVE HERE)
      as[[offset[plan SOME]]|[offset[settings SOME]]].
    - rewrite ACT in SOME;inversion SOME;congruence.
    - rewrite ATTR in SOME;discriminate. }
  destruct(gateway_attributes_initialize _ _ _ _ _ _ _ _ _ _ _ initializers before world result after next observed
    SIDE GENUINE VALID ATTR NATIVE POINTER ABSENT OPERATION)as[POST[status[RESULT BUILDERS]]].
  pose proof POST as POST_COPY;destruct POST_COPY as(NORMAL&AFTER_GENUINE&AFTER_VALID&ACCESS&PERMISSIONS&MEMORY&FRAME&STATUS&EXCLUSIVE&IO).
  exists status;split;[exact RESULT|]. split;[exact IO|].
  eapply gateway_sdk_post_context with(actions:=Some(Vptr actions Ptrofs.zero,[]))(attributes:=None)(before:=before)(world:=world);
    [exact DATA_SELECTED|exact CONTROL_SELECTED|exact ATTRIBUTES_DATA|exact ATTRIBUTES_CONTROL|exact ATTRIBUTES_READONLY|
      exact(conj FLAGS(conj GENUINE(conj ACT ATTR)))|exact POST| |].
  - rewrite BUILDERS;exact ACT.
  - rewrite BUILDERS;reflexivity.
Qed.
End Initializers.
