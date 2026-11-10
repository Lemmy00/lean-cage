(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Actual SDK output spans preserve the coupled launch context. *)
From Stdlib Require Import ZArith.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnResources GatewaySpawnRuntime
  GatewaySpawnActions GatewayPairContext GatewayExchangeFlagContext GatewaySDKContext GatewaySDKInputs.

Theorem gateway_sdk_post_context {World Event}(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)discipline(resources:World->gateway_resource_state)ipc
    readonly selected reference owner original(data_identity control_identity:gateway_pair_identity ipc)
    data control data_left data_right control_left control_right(builders:World->gateway_spawn_builders)(genuine:mem->World->Prop)
    actions attributes new_actions new_attributes before world after next observed object offset width:
  selected data->selected control->object<>data->object<>control->(forall position,~readonly object position)->
  gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right builders genuine actions attributes before world->
  gateway_builder_post io native stable discipline resources genuine before world after next observed object offset width->
  gateway_builder_actions(builders next)=new_actions->gateway_builder_attributes(builders next)=new_attributes->
  gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right builders genuine new_actions new_attributes after next.
Proof.
  intros DATA_SELECTED CONTROL_SELECTED DATA_SEPARATE CONTROL_SEPARATE READONLY_SEPARATE[INITIAL[GENUINE[ACT ATTR]]]
    (NORMAL&AFTER_GENUINE&VALID&ACCESS&PERMISSIONS&MEMORY&FRAME&STATUS&EXCLUSIVE&IO)ACTIONS ATTRIBUTES.
  split.
  - eapply gateway_flag_context_sdk_output;[exact DATA_SELECTED|exact CONTROL_SELECTED|exact DATA_SEPARATE|exact CONTROL_SEPARATE|
      exact READONLY_SEPARATE|exact INITIAL|exact NORMAL|exact ACCESS|exact PERMISSIONS|exact MEMORY|exact VALID|exact FRAME|
      exact STATUS|exact EXCLUSIVE].
  - split;[exact AFTER_GENUINE|]. split;assumption.
Qed.
