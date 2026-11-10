(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual local frees retain the published caller-owned fields. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayAllocation GatewayFieldStores.
Import ListNotations.
Open Scope Z_scope.

Definition field_locals_owned memory locals :Prop:=
  field_local_data locals<>field_local_size locals /\
  Mem.range_perm memory(field_local_data locals)0 8 Cur Freeable /\
  Mem.range_perm memory(field_local_size locals)0 8 Cur Freeable.

Definition field_local_release locals before after :Prop:=
  exists middle,Mem.free before(field_local_size locals)0 8=Some middle /\
    Mem.free middle(field_local_data locals)0 8=Some after.

Lemma actual_field_local_regions ge locals :
  blocks_of_env ge(field_environment locals)=
    [(field_local_size locals,0,8);(field_local_data locals,0,8)].
Proof. reflexivity. Qed.

Theorem actual_field_locals_release_exists ge memory locals :
  field_locals_owned memory locals ->
  exists after,field_local_release locals memory after /\
    Mem.free_list memory(blocks_of_env ge(field_environment locals))=Some after.
Proof.
  intros[DISTINCT[DATA SIZE]].
  destruct(Mem.range_perm_free _ _ _ _ SIZE)as[middle FREE_SIZE].
  assert(DATA_MIDDLE:Mem.range_perm middle(field_local_data locals)0 8 Cur Freeable).
  { intros position RANGE;eapply Mem.perm_free_1;
      [exact FREE_SIZE|left;congruence|apply DATA;exact RANGE]. }
  destruct(Mem.range_perm_free _ _ _ _ DATA_MIDDLE)as[after FREE_DATA].
  exists after;split;[exists middle;auto|].
  rewrite actual_field_local_regions;cbn;rewrite FREE_SIZE;cbn;rewrite FREE_DATA;reflexivity.
Qed.

Lemma field_locals_free_read_other locals before after object chunk offset :
  field_local_release locals before after ->
  object<>field_local_data locals ->object<>field_local_size locals ->
  Mem.loadv chunk after(Vptr object offset)=Mem.loadv chunk before(Vptr object offset).
Proof.
  intros[middle[SIZE DATA]] NOT_DATA NOT_SIZE.
  unfold Mem.loadv;destruct(zle(Ptrofs.unsigned offset+size_chunk chunk)Ptrofs.modulus);
    [|reflexivity].
  rewrite(Mem.load_free _ _ _ _ _ DATA)by auto.
  rewrite(Mem.load_free _ _ _ _ _ SIZE)by auto;reflexivity.
Qed.

Theorem actual_field_locals_free_keep_publication locals before after object offset kind size pointer owner :
  field_local_release locals before after ->
  object<>field_local_data locals ->object<>field_local_size locals ->
  field_wire_cells before object offset kind size pointer owner ->
  field_wire_cells after object offset kind size pointer owner.
Proof.
  intros FREE NOT_DATA NOT_SIZE[KIND[SIZE[DATA ROOT]]].
  unfold field_wire_cells.
  rewrite !field_locals_free_read_other with(locals:=locals)(before:=before)(after:=after)by assumption.
  exact(conj KIND(conj SIZE(conj DATA ROOT))).
Qed.
