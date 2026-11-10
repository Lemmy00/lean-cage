(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual writable caller storage produces the publication stores. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import ScalarMemory.
From HostGateway Require Import GatewayFieldStores.
Import ListNotations.
Open Scope Z_scope.

Definition field_storage_cells offset kind size pointer owner :=
  [{|scalar_chunk:=Mint32;scalar_offset:=Ptrofs.unsigned offset;scalar_value:=Vint kind|};
   {|scalar_chunk:=Mint64;scalar_offset:=Ptrofs.unsigned offset+8;scalar_value:=Vlong size|};
   {|scalar_chunk:=Mptr;scalar_offset:=Ptrofs.unsigned offset+16;scalar_value:=pointer|};
   {|scalar_chunk:=Mptr;scalar_offset:=Ptrofs.unsigned offset+24;scalar_value:=owner|}].

Definition field_borrowed_storage memory object offset capacity :Prop:=
  Ptrofs.unsigned offset+40<=capacity /\capacity<=Ptrofs.modulus /\
  (8|Ptrofs.unsigned offset) /\Mem.range_perm memory object 0 capacity Cur Freeable.

Lemma field_storage_cells_valid offset capacity kind size pointer owner :
  Ptrofs.unsigned offset+40<=capacity ->(8|Ptrofs.unsigned offset) ->
  Forall(scalar_valid capacity)(field_storage_cells offset kind size pointer owner).
Proof.
  intros BOUND[quotient ALIGN].
  pose proof(Ptrofs.unsigned_range offset)as RANGE.
  change(Forall(scalar_valid capacity)
    [{|scalar_chunk:=Mint32;scalar_offset:=Ptrofs.unsigned offset;scalar_value:=Vint kind|};
     {|scalar_chunk:=Mint64;scalar_offset:=Ptrofs.unsigned offset+8;scalar_value:=Vlong size|};
     {|scalar_chunk:=Mint64;scalar_offset:=Ptrofs.unsigned offset+16;scalar_value:=pointer|};
     {|scalar_chunk:=Mint64;scalar_offset:=Ptrofs.unsigned offset+24;scalar_value:=owner|}]).
  constructor.
  - unfold scalar_valid;cbn;split;[lia|]. split;[lia|]. exists(2*quotient);lia.
  - constructor.
    + unfold scalar_valid;cbn;split;[lia|]. split;[lia|].
      change(8|Ptrofs.unsigned offset+8);exists(quotient+1);lia.
    + constructor.
      * unfold scalar_valid;cbn;split;[lia|]. split;[lia|].
        change(8|Ptrofs.unsigned offset+16);exists(quotient+2);lia.
      * constructor;[|constructor].
        unfold scalar_valid;cbn;split;[lia|]. split;[lia|].
        change(8|Ptrofs.unsigned offset+24);exists(quotient+3);lia.
Qed.

Lemma field_scalar_stores_are_actual before object offset kind size pointer owner after :
  Ptrofs.unsigned offset+40<=Ptrofs.modulus ->
  scalar_stores object before(field_storage_cells offset kind size pointer owner)after ->
  field_store_sequence before object offset kind size pointer owner after.
Proof.
  intros BOUND STORES.
  inversion STORES as[|? ? ? first ? KIND REST];subst.
  inversion REST as[|? ? ? second ? SIZE REST2];subst.
  inversion REST2 as[|? ? ? third ? DATA REST3];subst.
  inversion REST3 as[|? ? ? last ? ROOT REST4];subst.
  inversion REST4;subst.
  exists first,second,third.
  cbn[scalar_chunk scalar_offset scalar_value]in KIND,SIZE,DATA,ROOT.
  assert(RAW:Ptrofs.unsigned offset+40<=Ptrofs.modulus)by exact BOUND.
  change Ptrofs.modulus with 18446744073709551616 in BOUND.
  unfold Mem.storev.
  rewrite !field_slot_no_wrap by lia.
  repeat rewrite zle_true by field_arithmetic.
  repeat split;try assumption.
  replace(Ptrofs.unsigned offset+0)with(Ptrofs.unsigned offset)by lia;exact KIND.
Qed.

Theorem actual_field_storage_produces_stores before object offset capacity kind size pointer owner :
  field_borrowed_storage before object offset capacity ->
  exists after,field_store_sequence before object offset kind size pointer owner after /\
    scalar_stores object before(field_storage_cells offset kind size pointer owner)after /\
    (forall block position access permission,
      Mem.perm after block position access permission<->Mem.perm before block position access permission).
Proof.
  intros[BOUND[LIMIT[ALIGN ACCESS]]].
  destruct(scalar_stores_exist object capacity(field_storage_cells offset kind size pointer owner)
    before(field_storage_cells_valid _ _ _ _ _ _ BOUND ALIGN)ACCESS)as[after STORES].
  exists after;split;[apply field_scalar_stores_are_actual;[lia|exact STORES]|].
  split;[exact STORES|exact(scalar_stores_permissions object before
    (field_storage_cells offset kind size pointer owner)after STORES)].
Qed.

Theorem actual_field_storage_preserves_other before object offset kind size pointer owner after
    block chunk position :
  scalar_stores object before(field_storage_cells offset kind size pointer owner)after ->
  block<>object ->Mem.load chunk after block position=Mem.load chunk before block position.
Proof. intros STORES OTHER;eapply scalar_stores_load_other;[exact STORES|auto]. Qed.
