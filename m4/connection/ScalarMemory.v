(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-structures.stores: Typed scalar stores and exact field transfer through struct copying. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Import ListNotations.
Open Scope Z_scope.

Record scalar_cell := { scalar_chunk : memory_chunk; scalar_offset : Z; scalar_value : val }.
Definition scalar_valid size cell :=
  0 <= scalar_offset cell /\ scalar_offset cell + size_chunk (scalar_chunk cell) <= size /\
  (align_chunk (scalar_chunk cell) | scalar_offset cell).
Definition scalar_separate a b :=
  scalar_offset a + size_chunk (scalar_chunk a) <= scalar_offset b \/
  scalar_offset b + size_chunk (scalar_chunk b) <= scalar_offset a.
Inductive scalar_stores b : mem -> list scalar_cell -> mem -> Prop :=
| scalar_stores_nil : forall m, scalar_stores b m [] m
| scalar_stores_cons : forall m cell tail mid after,
    Mem.store (scalar_chunk cell) m b (scalar_offset cell) (scalar_value cell) = Some mid ->
    scalar_stores b mid tail after -> scalar_stores b m (cell::tail) after.

Lemma scalar_stores_permissions : forall b m cells after,
  scalar_stores b m cells after -> forall block ofs kind perm,
  Mem.perm after block ofs kind perm <-> Mem.perm m block ofs kind perm.
Proof.
  intros b m cells after RUN; induction RUN; intros; [tauto|].
  rewrite IHRUN; split; eauto using Mem.perm_store_1, Mem.perm_store_2.
Qed.

Theorem scalar_stores_exist : forall b size cells m,
  Forall (scalar_valid size) cells -> Mem.range_perm m b 0 size Cur Freeable ->
  exists after, scalar_stores b m cells after.
Proof.
  intros b size cells m VALID; revert m. induction VALID; intros m RANGE.
  - exists m; constructor.
  - destruct H as [LOW [HIGH ALIGN]].
    assert (ACCESS : Mem.valid_access m (scalar_chunk x) b (scalar_offset x) Writable).
    { split; [|assumption]. red; intros pos BOUND. eapply Mem.perm_implies; [apply RANGE; lia|constructor]. }
    destruct (Mem.valid_access_store _ _ _ _ (scalar_value x) ACCESS) as [mid STORE].
    destruct (IHVALID mid) as [after TAIL].
    { red; intros; eapply Mem.perm_store_1; [exact STORE|apply RANGE; assumption]. }
    exists after; econstructor; eassumption.
Qed.

Lemma scalar_stores_load_other : forall b m cells after block chunk ofs,
  scalar_stores b m cells after ->
  (block <> b \/ Forall (fun c => ofs + size_chunk chunk <= scalar_offset c \/
     scalar_offset c + size_chunk (scalar_chunk c) <= ofs) cells) ->
  Mem.load chunk after block ofs = Mem.load chunk m block ofs.
Proof.
  intros b m cells after block chunk ofs RUN; induction RUN; intros SEP; [reflexivity|].
  rewrite IHRUN.
  - eapply Mem.load_store_other; [exact H|]. destruct SEP as [NE|CELLS]; [auto|].
    inversion CELLS; subst; tauto.
  - destruct SEP as [NE|CELLS]; [auto|]. inversion CELLS; subst; auto.
Qed.

Theorem scalar_stores_fields : forall b m cells after,
  scalar_stores b m cells after ->
  (forall before cell rest, cells = before ++ cell::rest -> Forall (scalar_separate cell) rest) ->
  forall cell, In cell cells ->
  Mem.load (scalar_chunk cell) after b (scalar_offset cell) =
    Some (Val.load_result (scalar_chunk cell) (scalar_value cell)).
Proof.
  intros b m cells after RUN; induction RUN; intros SEP current IN; [contradiction|].
  destruct IN as [SAME|IN]; [subst current|].
  - rewrite (scalar_stores_load_other _ _ _ _ _ _ _ RUN).
    + eapply Mem.load_store_same; exact H.
    + right. apply (SEP [] cell tail eq_refl).
  - apply IHRUN; [|exact IN]. intros before c rest EQ. apply (SEP (cell::before) c rest).
    cbn; congruence.
Qed.

Lemma loadbytes_slice : forall m b ofs bytes start count,
  Mem.loadbytes m b ofs (Z.of_nat (length bytes)) = Some bytes ->
  0 <= start -> 0 <= count -> start + count <= Z.of_nat (length bytes) ->
  Mem.loadbytes m b (ofs+start) count =
    Some (firstn (Z.to_nat count) (skipn (Z.to_nat start) bytes)).
Proof.
  intros m b ofs bytes start count LOAD START COUNT BOUND.
  replace (Z.of_nat (length bytes)) with (start + (Z.of_nat (length bytes)-start)) in LOAD by lia.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ LOAD ltac:(lia) ltac:(lia))
    as [front [suffix [FRONT [SUFFIX ALL]]]].
  replace (Z.of_nat (length bytes)-start) with (count+(Z.of_nat (length bytes)-start-count)) in SUFFIX by lia.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ SUFFIX ltac:(lia) ltac:(lia))
    as [middle [rest [MIDDLE [REST MORE]]]].
  pose proof (Mem.loadbytes_length _ _ _ _ _ FRONT) as LENF.
  pose proof (Mem.loadbytes_length _ _ _ _ _ MIDDLE) as LENM.
  rewrite ALL, <- LENF, skipn_app, skipn_all, Nat.sub_diag; cbn.
  rewrite MORE, <- LENM, firstn_app, firstn_all, Nat.sub_diag; cbn.
  rewrite app_nil_r. exact MIDDLE.
Qed.

Theorem copied_scalar_load : forall before after src dst sofs dofs bytes chunk offset v,
  Mem.loadbytes before src sofs (Z.of_nat (length bytes)) = Some bytes ->
  Mem.storebytes before dst dofs bytes = Some after ->
  0 <= offset -> offset + size_chunk chunk <= Z.of_nat (length bytes) ->
  (align_chunk chunk | dofs+offset) ->
  Mem.load chunk before src (sofs+offset) = Some v ->
  Mem.load chunk after dst (dofs+offset) = Some v.
Proof.
  intros before after src dst sofs dofs bytes chunk offset v LOAD STORE LOW HIGH ALIGN VALUE.
  pose proof (loadbytes_slice _ _ _ _ offset (size_chunk chunk) LOAD LOW
    ltac:(pose proof (size_chunk_pos chunk); lia) HIGH) as SOURCE.
  pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ STORE) as DEST.
  pose proof (loadbytes_slice _ _ _ _ offset (size_chunk chunk) DEST LOW
    ltac:(pose proof (size_chunk_pos chunk); lia) HIGH) as TARGET.
  destruct (Mem.load_valid_access _ _ _ _ _ VALUE) as [_ SALIGN].
  pose proof (Mem.loadbytes_load chunk _ _ _ _ SOURCE SALIGN) as SAME.
  assert (v = decode_val chunk (firstn (Z.to_nat (size_chunk chunk)) (skipn (Z.to_nat offset) bytes)))
    by congruence; subst v. eapply Mem.loadbytes_load; eassumption.
Qed.

Theorem scalar_stores_outside : forall b size m cells after,
  scalar_stores b m cells after -> Forall (scalar_valid size) cells ->
  Mem.unchanged_on (fun block pos => block <> b \/ pos < 0 \/ size <= pos) m after.
Proof.
  intros b size m cells after RUN; induction RUN; intros VALID; [apply Mem.unchanged_on_refl|].
  inversion VALID; subst. eapply Mem.unchanged_on_trans; [|apply IHRUN; assumption].
  eapply Mem.store_unchanged_on; [exact H|].
  intros pos BOUND [NE|[LOW|HIGH]]; destruct H2 as [A [B C]]; lia.
Qed.

Theorem scalar_free_exists : forall b size m cells after,
  scalar_stores b m cells after -> Mem.range_perm m b 0 size Cur Freeable ->
  exists freed, Mem.free after b 0 size = Some freed.
Proof.
  intros b size m cells after RUN RANGE.
  assert (AFTER : Mem.range_perm after b 0 size Cur Freeable).
  { red; intros ofs BOUND. apply (scalar_stores_permissions _ _ _ _ RUN); apply RANGE; assumption. }
  destruct (Mem.range_perm_free _ _ _ _ AFTER) as [freed FREE]; eauto.
Qed.

Definition scalar_validb size c :=
  Z.leb 0 (scalar_offset c) && Z.leb (scalar_offset c + size_chunk (scalar_chunk c)) size &&
  Z.eqb (Z.modulo (scalar_offset c) (align_chunk (scalar_chunk c))) 0.
Lemma scalar_validb_sound : forall size c, scalar_validb size c = true -> scalar_valid size c.
Proof.
  intros size c OK. unfold scalar_validb in OK.
  repeat rewrite Bool.andb_true_iff in OK. destruct OK as [[LOW HIGH] ALIGN].
  apply Z.leb_le in LOW; apply Z.leb_le in HIGH; apply Z.eqb_eq in ALIGN.
  split; [assumption|]. split; [assumption|]. apply Z.mod_divide; [pose proof (align_chunk_pos (scalar_chunk c)); lia|assumption].
Qed.

Lemma scalar_list_validb_sound : forall size cells,
  forallb (scalar_validb size) cells = true -> Forall (scalar_valid size) cells.
Proof.
  intros size cells VALID. apply Forall_forall; intros c IN.
  apply scalar_validb_sound. rewrite forallb_forall in VALID; apply VALID; assumption.
Qed.

Fixpoint scalar_orderedb cells :=
  match cells with
  | [] => true
  | c::rest => forallb (fun later => Z.leb (scalar_offset c + size_chunk (scalar_chunk c))
      (scalar_offset later)) rest && scalar_orderedb rest
  end.
Lemma scalar_orderedb_sound : forall cells,
  scalar_orderedb cells = true ->
  forall before c rest, cells = before ++ c::rest -> Forall (scalar_separate c) rest.
Proof.
  intros cells ORDER before; revert cells ORDER. induction before; intros cells ORDER c rest EQ; subst cells; cbn in ORDER.
  - apply Bool.andb_true_iff in ORDER; destruct ORDER as [HERE _].
    apply Forall_forall; intros later IN. rewrite forallb_forall in HERE.
    left. apply Z.leb_le; apply HERE; assumption.
  - apply Bool.andb_true_iff in ORDER; destruct ORDER as [_ TAIL]. eapply IHbefore; [exact TAIL|reflexivity].
Qed.
