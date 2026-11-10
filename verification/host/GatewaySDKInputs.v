(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Actual retained caller allocations supply writable SDK headers. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers Values Memory Clight.
From HostGateway Require Import GatewayThreadRuntime GatewayCallerBuffers GatewayCallerFamily GatewayBufferReference
  GatewaySpawnActions GatewaySpawnRuntime GatewaySpawnResources GatewayExchangeFlagContext GatewayPairContext.
Open Scope Z_scope.

Theorem gateway_flag_context_discipline {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    (strong weak:option val->mem->World->Prop)resources ipc readonly selected reference owner original
    data_identity control_identity data control data_left data_right control_left control_right left_mode right_mode memory world:
  (forall mode memory world,strong mode memory world->weak mode memory world)->
  gateway_flag_context native stable strong resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right left_mode right_mode memory world->
  gateway_flag_context native stable weak resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right left_mode right_mode memory world.
Proof. intros PROJECT[SIDE REST];split;[apply PROJECT;exact SIDE|exact REST]. Qed.

Lemma gateway_sdk_header_from_family {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    readonly selected reference owner memory world object width:
  gateway_caller_family native stable readonly selected reference owner memory world->selected object->
  Mem.range_perm reference object 0 width Cur Freeable->0<=width<=Ptrofs.modulus->
  native world object /\gateway_native_pointer memory object Ptrofs.zero width Writable.
Proof.
  intros FAMILY SELECTED PERMISSIONS WIDTH.
  destruct(FAMILY object SELECTED)as[LIVE[PRIVATE[READONLY[[FRAME CURRENT]REST]]]].
  split;[exact PRIVATE|]. split;[lia|]. split;[exact(proj2 WIDTH)|]. split;[exact LIVE|].
  intros position RANGE;eapply Mem.perm_implies.
  - apply(proj1(CURRENT object(or_introl eq_refl)position Cur Freeable));apply PERMISSIONS;exact RANGE.
  - constructor.
Qed.

Definition gateway_sdk_context {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    discipline(resources:World->gateway_resource_state)ipc readonly selected reference owner original
    (data_identity control_identity:gateway_pair_identity ipc)data control data_left data_right control_left control_right
    (builders:World->gateway_spawn_builders)(genuine:mem->World->Prop)actions attributes memory world:Prop:=
  gateway_flag_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right true false memory world /\genuine memory world /\
  gateway_builder_actions(builders world)=actions /\gateway_builder_attributes(builders world)=attributes.
