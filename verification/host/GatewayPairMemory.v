(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The actual descriptor slot store changes exactly the selected pair cell. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayThreadRuntime GatewaySpawnResources GatewaySpawnRuntime GatewayPairContext.
From HostGateway Require Import GatewayPairHistory GatewaySpawnDescriptors.
Open Scope Z_scope.

Definition pair_slot_value(index left right:Z):=if Z.eq_dec index 0 then left else right.
Definition pair_slot_left(index moved left:Z):=if Z.eq_dec index 0 then moved else left.
Definition pair_slot_right(index moved right:Z):=if Z.eq_dec index 0 then right else moved.
Definition pair_slot_entry ipc(identity:gateway_pair_identity ipc)index:=
  if Z.eq_dec index 0 then pair_left_entry ipc identity else pair_right_entry ipc identity.

Lemma gateway_pair_selected_load memory object offset left right index:
  gateway_pair_cells memory object offset left right->0<=index<2->
  Mem.load Mint32 memory object(Ptrofs.unsigned offset+4*index)=
    Some(Vint(Int.repr(pair_slot_value index left right))).
Proof.
  intros[CELLS[LEFT RIGHT]]RANGE;assert(index=0\/index=1)by lia;destruct H;subst index;
    cbn[pair_slot_value];[rewrite Z.add_0_r;exact LEFT|exact RIGHT].
Qed.

Lemma gateway_pair_slot_resources ipc(identity:gateway_pair_identity ipc)left right index state:
  gateway_pair_resources ipc identity left right state->0<=index<2->
  0<=pair_slot_value index left right<=Int.max_signed /\
  gateway_owned_descriptor state(pair_slot_value index left right)(pair_slot_entry ipc identity index).
Proof.
  intros[VALID[LBOUND[RBOUND[SEPARATE[LEFT[RIGHT REST]]]]]]RANGE.
  assert(index=0\/index=1)by lia;destruct H;subst index;cbn[pair_slot_value pair_slot_entry];auto.
Qed.

Lemma gateway_pair_cell_store_permissions before after object position value offset:
  Mem.store Mint32 before object position value=Some after->
  gateway_pair_output_cells before object offset->gateway_pair_output_cells after object offset.
Proof.
  intros STORE[[LENGTH[BOUND[LIVE RANGE]]][LEFT RIGHT]].
  split.
  - repeat split;try assumption.
    + eapply Mem.store_valid_block_1;eassumption.
    + intros query INSIDE;eapply Mem.perm_store_1;[exact STORE|apply RANGE;exact INSIDE].
  - split;eapply Mem.store_valid_access_1;eassumption.
Qed.

Lemma gateway_pair_cell_store memory object offset left right index moved:
  gateway_pair_cells memory object offset left right->0<=index<2->
  exists after,
    Mem.store Mint32 memory object(Ptrofs.unsigned offset+4*index)(Vint(Int.repr moved))=Some after /\
    gateway_pair_cells after object offset(pair_slot_left index moved left)(pair_slot_right index moved right).
Proof.
  intros[CELLS[LEFT RIGHT]]RANGE.
  assert(SLOT:Mem.valid_access memory Mint32 object(Ptrofs.unsigned offset+4*index)Writable).
  { assert(index=0\/index=1)by lia;destruct H;subst index;[rewrite Z.add_0_r;exact(proj1(proj2 CELLS))|
      exact(proj2(proj2 CELLS))]. }
  destruct(Mem.valid_access_store memory Mint32 object(Ptrofs.unsigned offset+4*index)(Vint(Int.repr moved))SLOT)
    as[after STORE];exists after;split;[exact STORE|].
  split;[eapply gateway_pair_cell_store_permissions;eassumption|].
  assert(index=0\/index=1)by lia;destruct H;subst index;cbn[pair_slot_left pair_slot_right]in *.
  - rewrite Z.add_0_r in STORE;split.
    + pose proof(Mem.load_store_same _ _ _ _ _ _ STORE)as LOAD;exact LOAD.
    + erewrite Mem.load_store_other;[exact RIGHT|exact STORE|right;right;cbn;lia].
  - split.
    + erewrite Mem.load_store_other;[exact LEFT|exact STORE|right;left;cbn;lia].
    + pose proof(Mem.load_store_same _ _ _ _ _ _ STORE)as LOAD;exact LOAD.
Qed.

Lemma gateway_pair_slot_duplicate ipc(identity:gateway_pair_identity ipc)left right moved index before after:
  gateway_pair_resources ipc identity left right before->gateway_resource_valid after->0<=index<2->
  gateway_duplicate_receipt before after(pair_slot_value index left right)4 moved(pair_slot_entry ipc identity index)->
  gateway_exclusive_kept before after->
  gateway_pair_resources ipc identity(pair_slot_left index moved left)(pair_slot_right index moved right)after /\
  moved<>pair_slot_value index left right /\4<=moved.
Proof.
  intros RESOURCES VALID RANGE DUPLICATE EXCLUSIVE.
  pose proof(gateway_duplicate_width _ _ _ _ _ _ DUPLICATE)as WIDTH.
  assert(index=0\/index=1)by lia;destruct H;subst index;
    cbn[pair_slot_value pair_slot_entry pair_slot_left pair_slot_right]in *.
  - destruct(gateway_pair_resources_duplicate_left ipc identity left right moved before after RESOURCES VALID DUPLICATE EXCLUSIVE)
      as[FINAL DIFFERENT];split;[exact FINAL|split;[exact DIFFERENT|lia]].
  - destruct(gateway_pair_resources_duplicate_right ipc identity left right moved before after RESOURCES VALID DUPLICATE EXCLUSIVE)
      as[FINAL DIFFERENT];split;[exact FINAL|split;[exact DIFFERENT|lia]].
Qed.

Lemma gateway_pair_replaced_other index left right moved:
  0<=index<2->left<>right->moved<>pair_slot_value index left right->
  pair_slot_left index moved left<>pair_slot_value index left right /\
  pair_slot_right index moved right<>pair_slot_value index left right.
Proof.
  intros RANGE SEPARATE DIFFERENT;assert(index=0\/index=1)by lia;destruct H;subst index;
    cbn[pair_slot_left pair_slot_right pair_slot_value]in *;intuition.
Qed.

Lemma gateway_pair_selected_lease_new ipc(identity:gateway_pair_identity ipc)left right index fd state:
  gateway_pair_resources ipc identity left right state->0<=index<2->
  gateway_owned_descriptor state fd(pair_slot_entry ipc identity index)->
  forall previous,gateway_owned_descriptor(pair_origin _ identity)fd previous->False.
Proof.
  intros RESOURCES RANGE CURRENT previous OLD.
  pose proof(gateway_pair_original_valid ipc identity left right state RESOURCES)as VALID.
  pose proof(gateway_pair_original_reference ipc identity left right state RESOURCES)as REFERENCE.
  assert(index=0\/index=1)by lia;destruct H;subst index;cbn[pair_slot_entry]in CURRENT.
  - eapply gateway_fresh_object_not_old_lease with(entry:=pair_left_entry ipc identity)
      (object:=pair_left_object _ identity);[exact VALID|exact REFERENCE|apply pair_left_fresh|reflexivity|exact CURRENT|exact OLD].
  - eapply gateway_fresh_object_not_old_lease with(entry:=pair_right_entry ipc identity)
      (object:=pair_right_object _ identity);[exact VALID|exact REFERENCE|apply pair_right_fresh|reflexivity|exact CURRENT|exact OLD].
Qed.
