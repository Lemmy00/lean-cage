(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Fresh scoped SDK state and actual ambient frames feed setup. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnRuntime GatewaySpawnResources
  GatewaySpawnActions GatewayPairContext GatewayExchangeFlagContext GatewaySDKInputs GatewayFramedRuntime.

Section RuntimeContext.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop)
    (builders:World->gateway_spawn_builders)(genuine:mem->World->Prop)(footprint:World->block->Z->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state)
    (data_identity control_identity:gateway_pair_identity ipc)(data control:block)(data_left data_right control_left control_right:Z).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control).

Theorem gateway_sdk_context_ambient actions attributes:
  gateway_ambient_closed backend(gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original
    data_identity control_identity data control data_left data_right control_left control_right builders genuine actions attributes).
Proof.
  intros before world after next[FLAGS[GENUINE[ACT ATTR]]]INTERFERENCE.
  destruct(gateway_builder_ambient _ _ _ _ _ _ _ _ _ sdk before world after next(proj1 FLAGS)GENUINE INTERFERENCE)
    as[BUILDERS AFTER].
  split.
  - eapply gateway_flag_context_ambient with(io:=io)(thread_errno:=thread_errno);eassumption.
  - split;[exact AFTER|]. rewrite BUILDERS;split;assumption.
Qed.

Theorem gateway_sdk_context_from_empty(stronger:option val->mem->World->Prop)memory world:
  (forall before current,stronger None before current->discipline None before current)->
  (forall before current,stronger None before current->gateway_builder_actions(builders current)=None /\
    gateway_builder_attributes(builders current)=None)->
  gateway_flag_context native stable stronger resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right true false memory world->
  gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right builders genuine None None memory world.
Proof.
  intros NORMAL EMPTY INITIAL.
  destruct(EMPTY memory world(proj1 INITIAL))as[ACT ATTR];split.
  - destruct INITIAL as[SIDE REST];split;[apply NORMAL;exact SIDE|exact REST].
  - split;[eapply gateway_builder_empty;[exact sdk|exact ACT|exact ATTR]|]. split;assumption.
Qed.
End RuntimeContext.
