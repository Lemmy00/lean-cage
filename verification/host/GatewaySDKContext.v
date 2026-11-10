(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: SDK header writes preserve the caller's other real buffers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayOperations
  GatewayCallerBuffers GatewayCallerFamily GatewaySpawnRuntime GatewaySpawnResources GatewayPairContext
  GatewayConnectionResources GatewayExchangeFlagContext GatewayPairBuffers.
Import ListNotations.

Theorem gateway_caller_family_output {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    readonly selected reference owner before world after next object offset width:
  gateway_caller_family native stable readonly selected reference owner before world->
  (forall position,~readonly object position)->gateway_access_retained native stable before world next->
  gateway_native_permissions before after object offset width->
  gateway_native_frame native stable(gateway_native_region object offset width)world before after->
  gateway_caller_family native stable readonly selected reference owner after next.
Proof.
  intros FAMILY DISJOINT ACCESS PERMISSIONS FRAME target SELECTED.
  eapply gateway_caller_buffers_operation;
    [exact(FAMILY target SELECTED)|exact ACCESS|exact FRAME|apply gateway_native_region_dec| | |].
  - intros other position HERE[SAME RANGE];subst other;exact(DISJOINT position HERE).
  - intros position kind permission[SAME RANGE];subst target;apply PERMISSIONS;exact RANGE.
  - intros other position READABLE[SAME RANGE];subst other.
    apply(proj1(PERMISSIONS position Cur Readable RANGE));exact READABLE.
Qed.

Theorem gateway_flag_context_sdk_output {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    discipline(resources:World->gateway_resource_state)ipc readonly selected reference owner original
    (data_identity control_identity:gateway_pair_identity ipc)data control data_left data_right control_left control_right
    left_mode right_mode before world after next object offset width:
  selected data->selected control->object<>data->object<>control->(forall position,~readonly object position)->
  gateway_flag_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right left_mode right_mode before world->
  discipline None after next->gateway_access_retained native stable before world next->
  gateway_native_permissions before after object offset width->
  gateway_native_frame native stable(gateway_native_region object offset width)world before after->
  gateway_resource_valid(resources next)->
  gateway_resource_frame(resources world)(resources next)(fun _=>False)(fun _=>False)->
  gateway_resource_status_frame(resources world)(resources next)(fun _=>False)->
  gateway_exclusive_kept(resources world)(resources next)->
  gateway_flag_context native stable discipline resources ipc readonly selected reference owner original data_identity control_identity
    data control data_left data_right control_left control_right left_mode right_mode after next.
Proof.
  intros DATA_SELECTED CONTROL_SELECTED DATA_SEPARATE CONTROL_SEPARATE READONLY_SEPARATE
    [SIDE[FAMILY[VALID[DATA[CONTROL[MODES[DATA_CELLS[CONTROL_CELLS ORIGINAL]]]]]]]]
    NORMAL ACCESS PERMISSIONS MEMORY AFTER FRAME STATUS EXCLUSIVE.
  split;[exact NORMAL|]. split.
  - eapply gateway_caller_family_output;[exact FAMILY|exact READONLY_SEPARATE|exact ACCESS|exact PERMISSIONS|exact MEMORY].
  - split;[exact AFTER|]. split;[eapply gateway_pair_leases_frame;[exact VALID|exact DATA|exact FRAME|exact EXCLUSIVE]|].
    split;[eapply gateway_pair_leases_frame;[exact VALID|exact CONTROL|exact FRAME|exact EXCLUSIVE]|].
    split;[eapply gateway_pair_modes_frame;[exact DATA|exact MODES|exact STATUS]|]. split.
    + eapply gateway_pair_cells_unchanged;[exact DATA_CELLS|].
      eapply gateway_native_frame_restrict;[exact MEMORY| |].
      * intros other position[SAME RANGE];subst other;left;exact(proj1(proj2(FAMILY data DATA_SELECTED))).
      * intros other position[SAME RANGE][SAME_OBJECT OUTPUT];congruence.
    + split.
      * eapply gateway_pair_cells_unchanged;[exact CONTROL_CELLS|].
        eapply gateway_native_frame_restrict;[exact MEMORY| |].
        -- intros other position[SAME RANGE];subst other;left;exact(proj1(proj2(FAMILY control CONTROL_SELECTED))).
        -- intros other position[SAME RANGE][SAME_OBJECT OUTPUT];congruence.
      * intros fd entry OLD;eapply(proj1 FRAME);[apply ORIGINAL;exact OLD|tauto].
Qed.
