(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Arithmetic meaning of the strictly imported decoder, without assuming its value. *)
From Stdlib Require Import Arith List Lia.
From LeanImport Require Import Lean.
Require Import ArgumentsImport ArgumentConnection.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Lemma argument_add_exact a b : nat_of_Nat (Nat_add a b) = nat_of_Nat a + nat_of_Nat b.
Proof.
  induction b as [|b IH].
  - change (nat_of_Nat a = nat_of_Nat a + 0); lia.
  - change (S (nat_of_Nat (Nat_add a b)) = nat_of_Nat a + S (nat_of_Nat b)); rewrite IH; lia.
Qed.

Lemma argument_mul_exact a b : nat_of_Nat (Nat_mul a b) = nat_of_Nat a * nat_of_Nat b.
Proof.
  induction b as [|b IH].
  - change (0 = nat_of_Nat a * 0); lia.
  - change (nat_of_Nat (Nat_add (Nat_mul a b) a) = nat_of_Nat a * S (nat_of_Nat b)).
    rewrite argument_add_exact, IH; lia.
Qed.

Lemma argument_pred_exact a : nat_of_Nat (Nat_pred a) = Nat.pred (nat_of_Nat a).
Proof. destruct a; reflexivity. Qed.

Lemma argument_sub_exact a b : nat_of_Nat (Nat_sub a b) = nat_of_Nat a - nat_of_Nat b.
Proof.
  revert a; induction b as [|b IH]; intro a.
  - change (nat_of_Nat a = nat_of_Nat a - 0); lia.
  - change (nat_of_Nat (Nat_pred (Nat_sub a b)) = nat_of_Nat a - S (nat_of_Nat b)).
    rewrite argument_pred_exact, IH; lia.
Qed.

Fixpoint argument_fold (initial : nat) (bytes : List_inst1 UInt8) : nat :=
  match bytes with
  | List_nil_inst1 _ => initial
  | List_cons_inst1 _ byte rest =>
    argument_fold (initial * 10 + (nat_of_Nat (UInt8_toNat byte) - 48)) rest
  end.

Lemma argument_digit_value limit initial byte value :
  LeanCage_Entry_Arguments_digit limit initial byte = Option_some_inst1 Nat value ->
  nat_of_Nat value = nat_of_Nat initial * 10 + (nat_of_Nat (UInt8_toNat byte) - 48).
Proof.
  intro RUN; unfold LeanCage_Entry_Arguments_digit in RUN.
  argument_branch RUN.
  - cbn zeta in RUN; argument_branch RUN.
    + discriminate.
    + injection RUN as SAME; subst value.
      change (nat_of_Nat (Nat_add (Nat_mul initial (Nat_of_nat 10))
        (Nat_sub (UInt8_toNat byte) (Nat_of_nat 48))) =
        nat_of_Nat initial * 10 + (nat_of_Nat (UInt8_toNat byte) - 48)).
      rewrite argument_add_exact, argument_mul_exact, argument_sub_exact; reflexivity.
  - discriminate.
Qed.

Theorem argument_digits_value limit bytes initial value :
  LeanCage_Entry_Arguments_digits limit initial bytes = Option_some_inst1 Nat value ->
  nat_of_Nat value = argument_fold (nat_of_Nat initial) bytes.
Proof.
  revert initial; induction bytes as [|byte rest IH]; intros initial RUN.
  - change (Option_some_inst1 Nat initial = Option_some_inst1 Nat value) in RUN.
    injection RUN as SAME; subst; reflexivity.
  - change (match LeanCage_Entry_Arguments_digit limit initial byte with
      | Option_none_inst1 _ => Option_none_inst1 Nat
      | Option_some_inst1 _ next => LeanCage_Entry_Arguments_digits limit next rest
      end = Option_some_inst1 Nat value) in RUN.
    destruct (LeanCage_Entry_Arguments_digit limit initial byte) as [|next] eqn:STEP; [discriminate|].
    rewrite (IH next RUN), (argument_digit_value _ _ _ _ STEP); reflexivity.
Qed.

Theorem argument_unsigned_value limit value bytes :
  Lean.eq (LeanCage_Entry_Arguments_unsigned limit bytes) (Option_some_inst1 Nat value) ->
  nat_of_Nat value = argument_fold 0 bytes.
Proof.
  intro EQ; assert (RUN : LeanCage_Entry_Arguments_unsigned limit bytes = Option_some_inst1 Nat value).
  { destruct EQ; reflexivity. }
  destruct bytes as [|first rest]; [discriminate RUN|].
  unfold LeanCage_Entry_Arguments_unsigned in RUN.
  cbn [LeanCage_Entry_Arguments_digits_match_1 List_casesOn_inst2 List_inst1_recl] in RUN.
  argument_branch RUN.
  - exact (argument_digits_value limit _ Nat_zero value RUN).
  - discriminate.
Qed.

Theorem imported_decimal_value bytes initial :
  nat_of_Nat (LeanCage_Entry_ArgumentMeaning_decimalValue initial bytes) =
    argument_fold (nat_of_Nat initial) bytes.
Proof.
  revert initial; induction bytes as [|byte rest IH]; intro initial.
  - reflexivity.
  - change (nat_of_Nat (LeanCage_Entry_ArgumentMeaning_decimalValue
      (Nat_add (Nat_mul initial (Nat_of_nat 10)) (Nat_sub (UInt8_toNat byte) (Nat_of_nat 48))) rest) =
      argument_fold (nat_of_Nat initial) (List_cons_inst1 UInt8 byte rest)).
    rewrite IH, argument_add_exact, argument_mul_exact, argument_sub_exact; reflexivity.
Qed.

Lemma argument_nat_injective a b : nat_of_Nat a = nat_of_Nat b -> a = b.
Proof. intro EQ; rewrite <- (Nat2natid a), <- (Nat2natid b); rewrite EQ; reflexivity. Qed.

(* This is the complete ordinary-Lean unsigned_value proposition, over imported computations. *)
Theorem imported_unsigned_value limit value bytes :
  Lean.eq (LeanCage_Entry_Arguments_unsigned limit bytes) (Option_some_inst1 Nat value) ->
  Lean.eq value (LeanCage_Entry_ArgumentMeaning_decimalValue Nat_zero bytes).
Proof.
  intro PARSED.
  assert (SAME : value = LeanCage_Entry_ArgumentMeaning_decimalValue Nat_zero bytes).
  { apply argument_nat_injective.
    rewrite (argument_unsigned_value _ _ _ PARSED), imported_decimal_value; reflexivity. }
  rewrite SAME; constructor.
Qed.
