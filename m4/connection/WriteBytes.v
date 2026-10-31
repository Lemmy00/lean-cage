(* SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later *)
(* §AR-m4-effects.writers: Byte ownership and exact, non-atomic store prefixes. *)
From Coq Require Import ZArith List Lia Logic.Classical_Prop.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events.
Import ListNotations.
Open Scope Z_scope.

(* The next three memory lemmas adapt common/Memory.v at CompCert commit
   14d616046360a0b2611ebdfc2f98368af402e1f7. The adaptation replaces its extra
   Axioms.proof_irr parameter with proof irrelevance derived from the already
   audited classical excluded middle. No upstream file is modified.

   The Compcert verified compiler
   Xavier Leroy, INRIA Paris-Rocquencourt
   Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt
   with contributions from Andrew Appel, Rob Dockins, and Gordon Stewart
   (Princeton University).
   Copyright Institut National de Recherche en Informatique et en Automatique.
   All rights reserved. These adapted lemmas use the upstream GNU Lesser General
   Public License option, version 2.1 or (at your option) any later version.
   The original file is also distributed under the INRIA Non-Commercial License
   Agreement. See ../LGPL-2.1.txt and LICENSES.md for the retained terms. *)

Lemma classical_memory_ext :
  forall cont1 cont2 acc1 acc2 next1 next2 a1 a2 b1 b2 c1 c2,
  cont1 = cont2 -> acc1 = acc2 -> next1 = next2 ->
  Mem.mkmem cont1 acc1 next1 a1 b1 c1 = Mem.mkmem cont2 acc2 next2 a2 b2 c2.
Proof. intros; subst; f_equal; apply Classical_Prop.proof_irrelevance. Qed.

Local Transparent Mem.store Mem.storebytes.

Lemma classical_store_bytes : forall m b ofs chunk v after,
  Mem.store chunk m b ofs v = Some after ->
  Mem.storebytes m b ofs (encode_val chunk v) = Some after.
Proof.
  unfold Mem.storebytes, Mem.store; intros.
  destruct (Mem.valid_access_dec m chunk b ofs Writable); inversion H; subst.
  destruct (Mem.range_perm_dec m b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable).
  - f_equal. apply classical_memory_ext; reflexivity.
  - destruct v0 as [RANGE ALIGN]. exfalso; apply n.
    rewrite encode_val_length, <- size_chunk_conv; exact RANGE.
Qed.

Lemma classical_bytes_concat : forall m b ofs first mid rest after,
  Mem.storebytes m b ofs first = Some mid ->
  Mem.storebytes mid b (ofs + Z.of_nat (length first)) rest = Some after ->
  Mem.storebytes m b ofs (first ++ rest) = Some after.
Proof.
  intros m b ofs first mid rest after FIRST REST.
  pose proof FIRST as F; pose proof REST as R.
  unfold Mem.storebytes in F, R |- *.
  destruct (Mem.range_perm_dec m b ofs (ofs + Z.of_nat (length first)) Cur Writable);
    try discriminate.
  destruct (Mem.range_perm_dec mid b (ofs + Z.of_nat (length first))
    (ofs + Z.of_nat (length first) + Z.of_nat (length rest)) Cur Writable);
    try discriminate.
  destruct (Mem.range_perm_dec m b ofs (ofs + Z.of_nat (length (first ++ rest))) Cur Writable).
  - inversion F; inversion R; subst; cbn. f_equal. apply classical_memory_ext; auto.
    rewrite PMap.gss, Mem.setN_concat. symmetry; apply PMap.set2.
  - exfalso; apply n. rewrite app_length, Nat2Z.inj_add. red; intros pos BOUND.
    destruct (zlt pos (ofs + Z.of_nat (length first))).
    + apply r; lia.
    + eapply Mem.perm_storebytes_2; [exact FIRST|]. apply r0; lia.
Qed.

Definition byte_encoding (x : int) : memval := Byte (Byte.repr (Int.unsigned x)).

Lemma byte_encoding_exact : forall x,
  encode_val Mint8unsigned (Vint x) = [byte_encoding x].
Proof. reflexivity. Qed.

Inductive byte_writes : mem -> block -> Z -> list int -> mem -> Prop :=
| bytes_done : forall m b ofs, byte_writes m b ofs [] m
| bytes_next : forall m b ofs x xs mid last,
    Mem.store Mint8unsigned m b ofs (Vint x) = Some mid ->
    byte_writes mid b (ofs + 1) xs last ->
    byte_writes m b ofs (x :: xs) last.

Lemma byte_writes_exists : forall values m b ofs,
  Mem.range_perm m b ofs (ofs + Z.of_nat (length values)) Cur Writable ->
  exists after, byte_writes m b ofs values after.
Proof.
  induction values as [|x xs IH]; intros m b ofs OWN.
  - exists m; constructor.
  - destruct (Mem.valid_access_store m Mint8unsigned b ofs (Vint x)) as [mid STORE].
    { split; [red; intros pos RANGE; apply OWN; change (ofs <= pos < ofs + 1) in RANGE; simpl length; rewrite Nat2Z.inj_succ; lia|apply Z.divide_1_l]. }
    destruct (IH mid b (ofs + 1)) as [after TAIL].
    { red; intros. eapply Mem.perm_store_1; [exact STORE|]. apply OWN.
      simpl length; rewrite Nat2Z.inj_succ; lia. }
    exists after; econstructor; eassumption.
Qed.

Lemma byte_writes_append : forall first second m b ofs mid last,
  byte_writes m b ofs first mid ->
  byte_writes mid b (ofs + Z.of_nat (length first)) second last ->
  byte_writes m b ofs (first ++ second) last.
Proof.
  intros first second m b ofs mid last FIRST; revert last second.
  induction FIRST; intros last' second SECOND; simpl app; simpl length in SECOND.
  - rewrite Z.add_0_r in SECOND; assumption.
  - econstructor; [eassumption|]. apply IHFIRST.
    rewrite Nat2Z.inj_succ in SECOND. replace (ofs + 1 + Z.of_nat (length xs))
      with (ofs + Z.succ (Z.of_nat (length xs))) by lia. assumption.
Qed.

Lemma byte_writes_storebytes : forall m b ofs values after,
  byte_writes m b ofs values after -> values <> [] ->
  Mem.storebytes m b ofs (map byte_encoding values) = Some after.
Proof.
  intros m b ofs values after RUN; induction RUN; intros NONEMPTY; [contradiction|].
  destruct xs as [|y ys].
  - inversion RUN; subst. cbn. rewrite <- byte_encoding_exact. apply classical_store_bytes; assumption.
  - cbn. change (byte_encoding x :: _) with ([byte_encoding x] ++ map byte_encoding (y :: ys)).
    eapply classical_bytes_concat.
    + rewrite <- byte_encoding_exact. apply classical_store_bytes; eassumption.
    + cbn. apply IHRUN; discriminate.
Qed.

Theorem byte_writes_permissions : forall m b ofs values after,
  byte_writes m b ofs values after ->
  forall other pos kind permission, Mem.perm after other pos kind permission <->
    Mem.perm m other pos kind permission.
Proof.
  intros m b ofs values after RUN; induction RUN; intros; [tauto|].
  rewrite IHRUN. split; eauto using Mem.perm_store_1, Mem.perm_store_2.
Qed.

Definition outside_bytes (b : block) ofs count other pos :=
  other <> b \/ pos < ofs \/ ofs + Z.of_nat count <= pos.

Theorem byte_writes_outside : forall m b ofs values after,
  byte_writes m b ofs values after ->
  Mem.unchanged_on (outside_bytes b ofs (length values)) m after.
Proof.
  intros m b ofs values after RUN. destruct values.
  - inversion RUN; subst; apply Mem.unchanged_on_refl.
  - eapply Mem.storebytes_unchanged_on.
    + apply byte_writes_storebytes; [exact RUN|discriminate].
    + rewrite map_length. unfold outside_bytes; intros pos RANGE [NE|[LOW|HIGH]]; cbn in *; lia.
Qed.

Theorem byte_writes_content : forall m b ofs values after,
  byte_writes m b ofs values after -> values <> [] ->
  Mem.loadbytes after b ofs (Z.of_nat (length values)) = Some (map byte_encoding values).
Proof.
  intros. rewrite <- (map_length byte_encoding values) at 1.
  eapply Mem.loadbytes_storebytes_same. apply byte_writes_storebytes; eassumption.
Qed.

Definition writer_prefix m b ofs values after :=
  exists first rest, values = first ++ rest /\ byte_writes m b ofs first after.

Lemma writer_prefix_initial : forall m b ofs values, writer_prefix m b ofs values m.
Proof. intros; exists [], values; split; [reflexivity|constructor]. Qed.

Lemma writer_prefix_final : forall m b ofs values after,
  byte_writes m b ofs values after -> writer_prefix m b ofs values after.
Proof. intros; exists values, []; rewrite app_nil_r; auto. Qed.

Theorem writer_prefix_content : forall m b ofs values after,
  writer_prefix m b ofs values after ->
  exists first rest, values = first ++ rest /\
    ((first = [] /\ after = m) \/
      (first <> [] /\ Mem.loadbytes after b ofs (Z.of_nat (length first)) =
        Some (map byte_encoding first))) /\
    Mem.unchanged_on (outside_bytes b ofs (length first)) m after /\
    (forall other pos kind permission, Mem.perm after other pos kind permission <->
      Mem.perm m other pos kind permission).
Proof.
  intros m b ofs values after [first [rest [SPLIT RUN]]]. exists first, rest.
  split; [assumption|]. split.
  - destruct first; [inversion RUN; subst; auto|right; split; [discriminate|]].
    eapply byte_writes_content; [exact RUN|discriminate].
  - split; [eapply byte_writes_outside|eapply byte_writes_permissions]; eassumption.
Qed.

Lemma pointer_byte_store : forall m b ofs index value after,
  0 <= index -> Ptrofs.unsigned ofs + index + 1 <= Ptrofs.modulus ->
  Mem.store Mint8unsigned m b (Ptrofs.unsigned ofs + index) (Vint value) = Some after ->
  Mem.storev Mint8unsigned m (Vptr b (Ptrofs.add ofs (Ptrofs.repr index))) (Vint value) = Some after.
Proof.
  intros m b ofs index value after NONNEG BOUND STORE.
  assert (U : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr index)) = Ptrofs.unsigned ofs + index).
  { rewrite Ptrofs.add_unsigned.
    rewrite (Ptrofs.unsigned_repr index) by
      (pose proof (Ptrofs.unsigned_range ofs); unfold Ptrofs.max_unsigned; lia).
    rewrite Ptrofs.unsigned_repr; [reflexivity|].
    pose proof (Ptrofs.unsigned_range ofs); unfold Ptrofs.max_unsigned; lia. }
  cbn. rewrite U. rewrite zle_true by exact BOUND. assumption.
Qed.

Theorem allocated_writer_input : forall base count,
  exists b m, Mem.alloc base 0 (Z.of_nat count) = (m, b) /\
    Mem.range_perm m b 0 (Z.of_nat count) Cur Writable.
Proof.
  intros base count. destruct (Mem.alloc base 0 (Z.of_nat count)) as [m b] eqn:ALLOC.
  exists b, m. split; [reflexivity|]. red; intros.
  eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; [exact ALLOC|assumption]|constructor].
Qed.
