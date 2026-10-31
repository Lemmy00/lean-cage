(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Exact copy arguments, including non-prefix interrupted copies. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Machine Library LibraryMachine.
Import ListNotations.
Open Scope Z_scope.

Lemma span_address_components : forall a b xs ys,
  span_bounds a xs -> span_bounds b ys -> address_block a = address_block b ->
  Ptrofs.unsigned (Ptrofs.repr (address_offset a)) =
    Ptrofs.unsigned (Ptrofs.repr (address_offset b)) -> a=b.
Proof.
  intros [ab ao] [bb bo] xs ys [A _] [B _] BLOCK SAME.
  cbn in *;subst bb. rewrite !Ptrofs.unsigned_repr in SAME by (unfold Ptrofs.max_unsigned;lia).
  subst bo;reflexivity.
Qed.

Lemma copy_arguments_unique : forall m source destination bytes src dst other,
  copy_owned m source destination bytes -> copy_owned m src dst other ->
  copy_args source destination bytes=copy_args src dst other ->
  source=src /\ destination=dst /\ bytes=other.
Proof.
  intros m source destination bytes src dst other [READ [BOUND [PERMS SEP]]]
    [READ' [BOUND' [PERMS' SEP']]] EQ.
  unfold copy_args,address_value in EQ;inversion EQ.
  assert (S : source=src) by (eapply readable_address_components;eassumption).
  assert (D : destination=dst) by (eapply span_address_components;eassumption).
  subst src dst. split;[reflexivity|]. split;[reflexivity|].
  eapply readable_bytes_unique;[exact READ|exact READ'|].
  assert (N : Int64.unsigned (Int64.repr (Z.of_nat (length bytes))) =
    Int64.unsigned (Int64.repr (Z.of_nat (length other)))) by congruence.
  pose proof READ as [[_ [_ MAX]] _];pose proof READ' as [[_ [_ MAX']] _].
  rewrite !Int64.unsigned_repr in N by lia. lia.
Qed.

Lemma memcpy_original_step : forall ge cell source destination bytes k m ev target,
  Machine.step ge cell (live (Callstate memcpy_definition (copy_args source destination bytes) k m)) ev target ->
  ev=loss_step /\ target=dead m.
Proof.
  intros ge cell source destination bytes k m ev target STEP.
  inversion STEP;subst;cbn in *;try contradiction;auto;
    match goal with H : boundary _ _ _ |- _ => inversion H;subst;destruct (operation q);discriminate end.
Qed.

Theorem memcpy_boundary_cases : forall ge cell source destination bytes k m ev target,
  copy_owned m source destination bytes ->
  library_step ge cell (live (Callstate memcpy_definition (copy_args source destination bytes) k m)) ev target ->
  (exists after, copy_result m source destination bytes after /\
    ev=memcpy_returned source destination bytes /\
    target=live (Returnstate (address_value destination) k after)) \/
  (exists schedule after, partial_copy destination bytes m schedule after /\
    ev=memcpy_lost source destination bytes schedule /\ target=dead after) \/
  (ev=library_wait /\ target=live (Callstate memcpy_definition (copy_args source destination bytes) k m)) \/
  (ev=original_event loss_step /\ target=dead m).
Proof.
  intros ge cell source destination bytes k m ev target OWN STEP.
  inversion STEP;subst;try discriminate;auto.
  - destruct (memcpy_original_step _ _ _ _ _ _ _ _ _ H) as [EV TARGET];subst;auto.
  - pose proof (proj1 H8) as OTHER.
    destruct OWN as [READ [BOUNDS REST]];destruct OTHER as [READ' [BOUNDS' REST']].
    assert (S : source0=source) by (eapply readable_address_components;eassumption).
    assert (D : destination0=destination) by (eapply span_address_components;eassumption).
    subst source0 destination0.
    change (Int64.unsigned (Int64.repr (Z.of_nat (length bytes0))) =
      Int64.unsigned (Int64.repr (Z.of_nat (length bytes)))) in H4.
    pose proof READ as [[_ [_ MAX]] _];pose proof READ' as [[_ [_ MAX']] _].
    rewrite !Int64.unsigned_repr in H4 by lia.
    assert (B : bytes0=bytes) by (eapply readable_bytes_unique;[exact READ'|exact READ|lia]).
    subst bytes0;left;exists after;auto.
  - match goal with OTHER : copy_owned _ _ _ _ |- _ =>
      lazymatch OTHER with OWN => fail | _ => pose proof OTHER as OWN' end end.
    destruct OWN as [READ [BOUNDS REST]];destruct OWN' as [READ' [BOUNDS' REST']].
    assert (S : source0=source) by (eapply readable_address_components;eassumption).
    assert (D : destination0=destination) by (eapply span_address_components;eassumption).
    subst source0 destination0.
    change (Int64.unsigned (Int64.repr (Z.of_nat (length bytes0))) =
      Int64.unsigned (Int64.repr (Z.of_nat (length bytes)))) in H4.
    pose proof READ as [[_ [_ MAX]] _];pose proof READ' as [[_ [_ MAX']] _].
    rewrite !Int64.unsigned_repr in H4 by lia.
    assert (B : bytes0=bytes) by (eapply readable_bytes_unique;[exact READ'|exact READ|lia]).
    subst bytes0;right;left;exists schedule,after;auto.
  all: repeat split;congruence.
Qed.
