(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Each selected SDK edit retains the exact action and attribute state. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI GatewaySpawnRuntime
  GatewaySpawnResources GatewaySpawnActions GatewaySpawnDescriptors GatewayPairContext GatewayCallerFamily GatewayExchangeFlagContext
  GatewaySDKInputs GatewaySDKPost.
Import ListNotations.
Open Scope Z_scope.

Section Mutations.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (resources:World->gateway_resource_state)(ipc:nat->Prop)(builders:World->gateway_spawn_builders)
    (genuine:mem->World->Prop)(footprint:World->block->Z->Prop).
Context(sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state)
    (data_identity control_identity:gateway_pair_identity ipc)(data control:block)(data_left data_right control_left control_right:Z)
    (actions attributes:block).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(ACTIONS_SELECTED:selected actions)(ATTRIBUTES_SELECTED:selected attributes)
    (ACTIONS_DATA:actions<>data)(ACTIONS_CONTROL:actions<>control)(ATTRIBUTES_DATA:attributes<>data)(ATTRIBUTES_CONTROL:attributes<>control)
    (ACTIONS_READONLY:forall position,~readonly actions position)(ATTRIBUTES_READONLY:forall position,~readonly attributes position)
    (ACTIONS_RANGE:Mem.range_perm reference actions 0 80 Cur Freeable)
    (ATTRIBUTES_RANGE:Mem.range_perm reference attributes 0 336 Cur Freeable).
Local Definition context:=gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original
  data_identity control_identity data control data_left data_right control_left control_right builders genuine.

Theorem actual_sdk_attributes_update request plan settings before world result after next observed:
  gateway_attribute_request_valid request->context(Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings))before world->
  gateway_spawn_operation backend(gateway_attribute_request_api request)
    (gateway_attribute_request_arguments request(Vptr attributes Ptrofs.zero))before world result after next observed->
  exists status,result=Vint status /\io observed=None /\
    context(Some(Vptr actions Ptrofs.zero,plan))
      (Some(Vptr attributes Ptrofs.zero,if Int.eq status Int.zero then gateway_attribute_request_value request settings else settings))after next.
Proof.
  intros REQUEST INITIAL OPERATION;destruct INITIAL as[FLAGS[GENUINE[ACT ATTR]]].
  pose proof(proj1 FLAGS)as SIDE;pose proof(proj1(proj2(proj2 FLAGS)))as VALID.
  destruct(gateway_sdk_header_from_family native stable readonly selected reference owner before world attributes 336
    (proj1(proj2 FLAGS))ATTRIBUTES_SELECTED ATTRIBUTES_RANGE ltac:(change(0<=336<=18446744073709551616);lia))
    as[NATIVE POINTER].
  destruct(gateway_attributes_update _ _ _ _ _ _ _ _ _ sdk request before world attributes Ptrofs.zero settings result after next observed
    SIDE GENUINE VALID NATIVE POINTER eq_refl ATTR REQUEST OPERATION)as[POST[status[RESULT BUILDERS]]].
  pose proof POST as POST_COPY;destruct POST_COPY as(NORMAL&AFTER_GENUINE&AFTER_VALID&ACCESS&PERMISSIONS&MEMORY&FRAME&STATUS&EXCLUSIVE&IO).
  exists status;split;[exact RESULT|]. split;[exact IO|].
  eapply gateway_sdk_post_context with(actions:=Some(Vptr actions Ptrofs.zero,plan))
    (attributes:=Some(Vptr attributes Ptrofs.zero,settings))(before:=before)(world:=world);
    [exact DATA_SELECTED|exact CONTROL_SELECTED|exact ATTRIBUTES_DATA|exact ATTRIBUTES_CONTROL|exact ATTRIBUTES_READONLY|
      exact(conj FLAGS(conj GENUINE(conj ACT ATTR)))|exact POST| |].
  - rewrite BUILDERS;exact ACT.
  - rewrite BUILDERS;reflexivity.
Qed.

Theorem actual_sdk_actions_append request plan settings before world result after next observed:
  gateway_action_request_valid request->context(Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings))before world->
  gateway_spawn_operation backend(gateway_action_request_api request)
    (gateway_action_request_arguments request(Vptr actions Ptrofs.zero))before world result after next observed->
  exists status,result=Vint status /\io observed=None /\
    context(Some(Vptr actions Ptrofs.zero,if Int.eq status Int.zero then plan++[gateway_action_request_value request]else plan))
      (Some(Vptr attributes Ptrofs.zero,settings))after next.
Proof.
  intros REQUEST INITIAL OPERATION;destruct INITIAL as[FLAGS[GENUINE[ACT ATTR]]].
  pose proof(proj1 FLAGS)as SIDE;pose proof(proj1(proj2(proj2 FLAGS)))as VALID.
  destruct(gateway_sdk_header_from_family native stable readonly selected reference owner before world actions 80
    (proj1(proj2 FLAGS))ACTIONS_SELECTED ACTIONS_RANGE ltac:(change(0<=80<=18446744073709551616);lia))
    as[NATIVE POINTER].
  destruct(gateway_actions_append _ _ _ _ _ _ _ _ _ sdk request before world actions Ptrofs.zero plan result after next observed
    SIDE GENUINE VALID NATIVE POINTER eq_refl ACT REQUEST OPERATION)as[POST[status[RESULT BUILDERS]]].
  pose proof POST as POST_COPY;destruct POST_COPY as(NORMAL&AFTER_GENUINE&AFTER_VALID&ACCESS&PERMISSIONS&MEMORY&FRAME&STATUS&EXCLUSIVE&IO).
  exists status;split;[exact RESULT|]. split;[exact IO|].
  eapply gateway_sdk_post_context with(actions:=Some(Vptr actions Ptrofs.zero,plan))
    (attributes:=Some(Vptr attributes Ptrofs.zero,settings))(before:=before)(world:=world);
    [exact DATA_SELECTED|exact CONTROL_SELECTED|exact ACTIONS_DATA|exact ACTIONS_CONTROL|exact ACTIONS_READONLY|
      exact(conj FLAGS(conj GENUINE(conj ACT ATTR)))|exact POST| |].
  - rewrite BUILDERS;reflexivity.
  - rewrite BUILDERS;exact ATTR.
Qed.
End Mutations.
