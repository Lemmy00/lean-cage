(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.writeall: Whole-buffer preservation and exact suffix ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import IO.
Import ListNotations.
Open Scope Z_scope.

Definition write_owned (q : request) (bytes : list Byte.int) (m : mem) : Prop :=
  operation q = writing /\ owned q m /\
  Z.of_nat (length bytes) = requested q /\
  Mem.loadbytes m (buffer_block q) (buffer_offset q) (requested q) = Some (map Byte bytes).

Lemma write_owned_errno : forall q bytes m error m',
  write_owned q bytes m -> errno_change q m error m' -> write_owned q bytes m'.
Proof.
  intros q bytes m error m' [OP [OWN [LEN LOAD]]] CHANGE.
  pose proof OWN as O.
  destruct OWN as [SIZE [OFFSET [WRAP [EO [EW [ACCESS [SEP BUF]]]]]]].
  assert (LOAD' : Mem.loadbytes m' (buffer_block q) (buffer_offset q) (requested q) = Some (map Byte bytes)).
  { rewrite (errno_change_preserves_buffer q m error m' (requested q)); auto; lia. }
  split; [exact OP|]. split; [|auto].
  unfold owned; rewrite OP.
  split; [exact SIZE|]. split; [exact OFFSET|]. split; [exact WRAP|].
  split; [exact EO|]. split; [exact EW|]. split.
  - inversion CHANGE; subst; [exact ACCESS|]. eapply Mem.store_valid_access_1; eauto.
  - split; [exact SEP|]. exists bytes; auto.
Qed.

Lemma append_same_length : forall (A : Type) (a b c d : list A),
  length a = length c -> a ++ b = c ++ d -> a = c /\ b = d.
Proof.
  intros A a; induction a as [|x a IH]; intros b c d LEN EQ;
    destruct c as [|y c]; simpl in *; try discriminate.
  - auto.
  - inversion EQ; subst. destruct (IH b c d) as [AC BD]; [lia|assumption|]. subst; auto.
Qed.

Lemma load_suffix : forall m b ofs (done rest : list Byte.int),
  Mem.loadbytes m b ofs (Z.of_nat (length (done ++ rest))) = Some (map Byte (done ++ rest)) ->
  Mem.loadbytes m b (ofs + Z.of_nat (length done)) (Z.of_nat (length rest)) = Some (map Byte rest).
Proof.
  intros m b ofs done rest LOAD.
  rewrite app_length, Nat2Z.inj_add, map_app in LOAD.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ LOAD) as [a [c [A [C EQ]]]]; try lia.
  assert (LEN : length a = length (map Byte done)).
  { erewrite Mem.loadbytes_length by exact A. rewrite Nat2Z.id, map_length; reflexivity. }
  destruct (append_same_length _ a c (map Byte done) (map Byte rest) LEN (eq_sym EQ)); subst; assumption.
Qed.

Lemma map_byte_injective : forall (a b : list Byte.int), map Byte a = map Byte b -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; simpl; intros H; try discriminate; auto.
  inversion H; subst. f_equal; auto.
Qed.

Lemma load_prefix : forall m b ofs (rest bytes : list Byte.int),
  Mem.loadbytes m b ofs (Z.of_nat (length rest)) = Some (map Byte rest) ->
  Mem.loadbytes m b ofs (Z.of_nat (length bytes)) = Some (map Byte bytes) ->
  Z.of_nat (length bytes) <= Z.of_nat (length rest) ->
  exists remaining, rest = bytes ++ remaining.
Proof.
  intros m b ofs rest bytes FULL PART SIZE.
  replace (Z.of_nat (length rest)) with
    (Z.of_nat (length bytes) + (Z.of_nat (length rest) - Z.of_nat (length bytes))) in FULL by lia.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ FULL) as [a [c [A [C EQ]]]]; try lia.
  assert (a = map Byte bytes) by congruence. subst a.
  assert (LEN : (length bytes <= length rest)%nat) by lia.
  exists (skipn (length bytes) rest).
  assert (MAP : map Byte (firstn (length bytes) rest) = map Byte bytes).
  { rewrite <- firstn_map. rewrite EQ, firstn_app.
    rewrite map_length, Nat.sub_diag; simpl. rewrite firstn_all2 by (rewrite map_length; lia). apply app_nil_r. }
  assert (PREFIX : firstn (length bytes) rest = bytes).
  { apply map_byte_injective; exact MAP. }
  rewrite <- PREFIX at 1. symmetry; apply firstn_skipn.
Qed.

Lemma load_first : forall m b ofs (first rest : list Byte.int),
  Mem.loadbytes m b ofs (Z.of_nat (length (first ++ rest))) = Some (map Byte (first ++ rest)) ->
  Mem.loadbytes m b ofs (Z.of_nat (length first)) = Some (map Byte first).
Proof.
  intros m b ofs first rest LOAD. rewrite app_length, Nat2Z.inj_add, map_app in LOAD.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ LOAD) as [a [c [A [C EQ]]]]; try lia.
  assert (LEN : length a = length (map Byte first)).
  { erewrite Mem.loadbytes_length by exact A. rewrite Nat2Z.id, map_length; reflexivity. }
  destruct (append_same_length _ a c (map Byte first) (map Byte rest) LEN (eq_sym EQ)); subst; assumption.
Qed.
