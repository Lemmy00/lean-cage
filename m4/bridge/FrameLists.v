(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import Arith List Lia.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Import ListNotations.

Lemma imported_length_exact A (xs : List_inst1 A) :
 nat_of_Nat (List_length_inst1 A xs) = List.length (standard_list xs).
Proof.
 induction xs as [|x xs IH]; [reflexivity|].
 change (S (nat_of_Nat (List_length_inst1 A xs)) = S (List.length (standard_list xs))).
 now rewrite IH.
Qed.
Lemma imported_concat_exact A (xs : List_inst1 A) x :
 standard_list (List_concat_inst1 A xs x) = standard_list xs ++ [x].
Proof.
 induction xs as [|y xs IH]; [reflexivity|].
 change (y :: standard_list (List_concat_inst1 A xs x) = y :: (standard_list xs ++ [x])).
 now rewrite IH.
Qed.
Lemma imported_get_exact A (xs : List_inst1 A) i
 (h : Nat_le (Nat_succ i) (List_length_inst1 A xs)) (default : A) :
 List_get_inst1 A xs (Fin_mk _ i h) = nth (nat_of_Nat i) (standard_list xs) default.
Proof.
 revert i h; induction xs as [|x xs IH]; intros i h.
 - pose proof (Nat_le_nat_le' _ _ h) as BAD.
   change (S (nat_of_Nat i) <= 0) in BAD; lia.
 - destruct i as [|i]; [reflexivity|].
   apply IH.
Qed.
Definition standard_bool (b : Bool) : bool :=
 match b with Bool_false => false | Bool_true => true end.
Lemma imported_beq_exact a b :
 standard_bool (Nat_beq a b) = Nat.eqb (nat_of_Nat a) (nat_of_Nat b).
Proof.
 revert b; induction a as [|a IH]; intros [|b]; try reflexivity.
 change (standard_bool (Nat_beq a b) = Nat.eqb (nat_of_Nat a) (nat_of_Nat b)); apply IH.
Qed.
Lemma imported_ble_exact a b :
 standard_bool (Nat_ble a b) = Nat.leb (nat_of_Nat a) (nat_of_Nat b).
Proof.
 revert b; induction a as [|a IH]; intros [|b]; try reflexivity.
 change (standard_bool (Nat_ble a b) = Nat.leb (nat_of_Nat a) (nat_of_Nat b)); apply IH.
Qed.

Lemma imported_dite_true (A : Type) (p : SProp) (d : Decidable p)
 (t : p -> A) (e : Not p -> A) (h : p) : dite A p d t e = t h.
Proof.
 destruct d as [b reflect]; destruct b.
 - destruct (reflect h).
 - reflexivity.
Qed.
Lemma imported_dite_false (A : Type) (p : SProp) (d : Decidable p)
 (t : p -> A) (e : Not p -> A) (h : Not p) : dite A p d t e = e h.
Proof.
 destruct d as [b reflect]; destruct b.
 - reflexivity.
 - destruct (h reflect).
Qed.
Lemma imported_ite_true (A : Type) (p : SProp) (d : Decidable p) (t e : A) (h : p) :
 ite A p d t e = t.
Proof. exact (imported_dite_true A p d (fun _ => t) (fun _ => e) h). Qed.
Lemma imported_ite_false (A : Type) (p : SProp) (d : Decidable p) (t e : A) (h : Not p) :
 ite A p d t e = e.
Proof. exact (imported_dite_false A p d (fun _ => t) (fun _ => e) h). Qed.
Lemma imported_not_le a b : nat_of_Nat b < nat_of_Nat a -> Not (Nat_le a b).
Proof. intros LT LE; pose proof (Nat_le_nat_le' _ _ LE); exfalso; lia. Qed.
Lemma imported_pred_exact a : nat_of_Nat (Nat_pred a) = Nat.pred (nat_of_Nat a).
Proof. destruct a; reflexivity. Qed.
Lemma imported_sub_exact a b :
 nat_of_Nat (Nat_sub a b) = Nat.sub (nat_of_Nat a) (nat_of_Nat b).
Proof.
 induction b as [|b IH].
 - change (nat_of_Nat a = nat_of_Nat a - 0); lia.
 - change (nat_of_Nat (Nat_pred (Nat_sub a b)) = nat_of_Nat a - S (nat_of_Nat b)).
   rewrite imported_pred_exact, IH; lia.
Qed.
Lemma imported_min_exact a b :
 nat_of_Nat (Min_min_inst1 Nat instMinNat a b) = Nat.min (nat_of_Nat a) (nat_of_Nat b).
Proof.
 change (nat_of_Nat (ite Nat (Nat_le a b) (Nat_decLe a b) a b) =
   Nat.min (nat_of_Nat a) (nat_of_Nat b)).
 destruct (le_dec (nat_of_Nat a) (nat_of_Nat b)) as [LE|GT].
 - rewrite (imported_ite_true Nat _ _ a b (nat_le_Nat_le a b LE)).
   symmetry; apply Nat.min_l; assumption.
 - rewrite (imported_ite_false Nat _ _ a b (imported_not_le a b ltac:(lia))).
   symmetry; apply Nat.min_r; lia.
Qed.
