(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Each actual edit has its own typed status and precise shadow
   effect. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewaySpawnABI GatewaySpawnActions
  GatewaySpawnRuntime GatewaySpawnResources GatewaySpawnDescriptors GatewayPairContext GatewayConnectionResources
  GatewaySDKInputs GatewaySDKMutation GatewaySDKEditSource.
Import ListNotations.
Open Scope Z_scope.

Definition sdk_edit_plan edit status data_right control_right plan:=match edit with
  gateway_edit_input=>if Int.eq status Int.zero then plan++[gateway_spawn_dup data_right 0]else plan|
  gateway_edit_output=>if Int.eq status Int.zero then plan++[gateway_spawn_dup data_right 1]else plan|
  gateway_edit_cancellation=>if Int.eq status Int.zero then plan++[gateway_spawn_dup control_right 3]else plan|
  gateway_edit_closefrom=>if Int.eq status Int.zero then plan++[gateway_spawn_closefrom 4]else plan|_=>plan end.
Definition sdk_edit_settings edit status settings:=match edit with
  gateway_edit_group=>if Int.eq status Int.zero then gateway_attribute_request_value(gateway_set_group Int.zero)settings else settings|
  gateway_edit_flags=>if Int.eq status Int.zero then gateway_attribute_request_value(gateway_set_spawn_flags(Int.repr 2))settings else settings|
  _=>settings end.

Section Edits.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (resources:World->gateway_resource_state)(ipc:nat->Prop)(builders:World->gateway_spawn_builders)
    (genuine:mem->World->Prop)(footprint:World->block->Z->Prop).
Context(sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state)
    (data_identity control_identity:gateway_pair_identity ipc)(data control:block)(data_left data_right control_left control_right:Z)
    (actions attributes:block).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(ACTIONS_SELECTED:selected actions)
    (ATTRIBUTES_SELECTED:selected attributes)(ACTIONS_DATA:actions<>data)(ACTIONS_CONTROL:actions<>control)
    (ATTRIBUTES_DATA:attributes<>data)(ATTRIBUTES_CONTROL:attributes<>control)
    (ACTIONS_READONLY:forall position,~readonly actions position)(ATTRIBUTES_READONLY:forall position,~readonly attributes position)
    (ACTIONS_RANGE:Mem.range_perm reference actions 0 80 Cur Freeable)
    (ATTRIBUTES_RANGE:Mem.range_perm reference attributes 0 336 Cur Freeable).
Local Definition context plan settings:=gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original
  data_identity control_identity data control data_left data_right control_left control_right builders genuine
  (Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings)).

Theorem actual_sdk_edit_effect edit plan settings before world result after next observed:
  context plan settings before world->
  gateway_spawn_operation backend(sdk_edit_api edit)(sdk_edit_arguments edit actions attributes data_right control_right)
    before world result after next observed->
  exists status,result=Vint status /\io observed=None /\
    context(sdk_edit_plan edit status data_right control_right plan)(sdk_edit_settings edit status settings)after next.
Proof.
  intros INITIAL OPERATION.
  assert(DATA_BOUND:0<=data_right<=Int.max_signed).
  { exact(gateway_pair_lease_right_width _ _ _ _ _(proj1(proj2(proj2(proj2(proj1 INITIAL)))))). }
  assert(CONTROL_BOUND:0<=control_right<=Int.max_signed).
  { exact(gateway_pair_lease_right_width _ _ _ _ _(proj1(proj2(proj2(proj2(proj2(proj1 INITIAL))))))). }
  destruct edit;unfold context;cbn[sdk_edit_plan sdk_edit_settings].
  - eapply actual_sdk_attributes_update with(request:=gateway_set_group Int.zero);
      try eassumption;cbn[gateway_attribute_request_valid];change(0<=0);lia.
  - eapply actual_sdk_attributes_update with(request:=gateway_set_spawn_flags(Int.repr 2));
      try eassumption;reflexivity.
  - eapply actual_sdk_actions_append with(request:=gateway_add_dup data_right 0);
      try eassumption;cbn[gateway_action_request_valid];split;[exact DATA_BOUND|change(0<=0<=2147483647);lia].
  - eapply actual_sdk_actions_append with(request:=gateway_add_dup data_right 1);
      try eassumption;cbn[gateway_action_request_valid];split;[exact DATA_BOUND|change(0<=1<=2147483647);lia].
  - eapply actual_sdk_actions_append with(request:=gateway_add_dup control_right 3);
      try eassumption;cbn[gateway_action_request_valid];split;[exact CONTROL_BOUND|change(0<=3<=2147483647);lia].
  - eapply actual_sdk_actions_append with(request:=gateway_add_closefrom 4);
      try eassumption;cbn[gateway_action_request_valid];change(0<=4<=2147483647);lia.
Qed.
End Edits.
