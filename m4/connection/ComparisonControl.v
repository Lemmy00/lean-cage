(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Complete finite-width memcmp boundary for actual decoder callers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Machine Library LibraryMachine.
Import ListNotations.
Open Scope Z_scope.

Lemma memcmp_original_step : forall ge cell left right count k m ev target,
  Machine.step ge cell
    (live (Callstate memcmp_definition (comparison_args left right count) k m)) ev target ->
  ev = loss_step /\ target = dead m.
Proof.
  intros ge cell left right count k m ev target STEP. inversion STEP; subst; cbn in *;
    try contradiction; auto;
    match goal with H : boundary _ _ _ |- _ => inversion H; subst; destruct (operation q); discriminate end.
Qed.

Theorem memcmp_boundary_cases : forall ge cell left right count k m ev target,
  memcmp_owned m left right count ->
  library_step ge cell
    (live (Callstate memcmp_definition (comparison_args left right count) k m)) ev target ->
  (exists value, memcmp_result m left right count value /\
    ev = memcmp_returned left right count value /\ target = live (Returnstate (Vint value) k m)) \/
  (ev = library_wait /\ target = live (Callstate memcmp_definition (comparison_args left right count) k m)) \/
  (ev = original_event loss_step /\ target = dead m).
Proof.
  intros ge cell left right count k m ev target [xs [ys [LEFT [RIGHT [SIZE LENGTH]]]]] STEP.
  inversion STEP; subst; try discriminate; auto.
  - destruct (memcmp_original_step _ _ _ _ _ _ _ _ _ H) as [EV TARGET]; subst; auto.
  - left. exists value.
    match goal with RES : memcmp_result _ _ _ _ _ |- _ =>
      destruct RES as [a [b [A [B [N [LEN RESULT]]]]]] end.
    assert (L : left0 = left).
    { eapply readable_address_components; [exact A|exact LEFT|eassumption|eassumption]. }
    assert (R : right0 = right).
    { eapply readable_address_components; [exact B|exact RIGHT|eassumption|eassumption]. }
    assert (C : count0 = Z.of_nat (length xs)).
    { change (Int64.unsigned (Int64.repr count0) =
        Int64.unsigned (Int64.repr (Z.of_nat (length xs)))) in H4.
      pose proof A as [[_ [_ MAXA]] _]. pose proof LEFT as [[_ [_ MAXX]] _].
      rewrite !Int64.unsigned_repr in H4 by lia. exact H4. }
    subst. split; [exists a,b; auto|auto].
  all: split; congruence.
Qed.
