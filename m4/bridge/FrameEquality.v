(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import Arith List Lia Bool.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat FrameLists FrameArray.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Import ListNotations.

Lemma imported_equality_standard A (a b : A) (h : Lean.eq a b) : a = b.
Proof. destruct h; reflexivity. Qed.
Lemma standard_equality_imported A (a b : A) : a = b -> Lean.eq a b.
Proof. intros H; subst; constructor. Qed.
Lemma standard_bool_and a b : standard_bool (Bool_and a b) = andb (standard_bool a) (standard_bool b).
Proof. destruct a,b; reflexivity. Qed.
Lemma decide_equality_exact A (dec : DecidableEq A) a b :
 standard_bool (Decidable_decide (Lean.eq a b) (dec a b)) = true <-> a = b.
Proof.
 destruct (dec a b) as [v h]; destruct v; cbn [Decidable_decide standard_bool].
 - split; [discriminate|]. intro H; destruct (h (standard_equality_imported A a b H)).
 - split; [intro H; exact (imported_equality_standard A a b h)|reflexivity].
Qed.
Lemma array_eq_aux_exact A (xs ys : Array_inst1 A) hsz (p : A -> A -> Bool)
 (GOOD : forall a b, standard_bool (p a b) = true <-> a = b)
 i (hi : Nat_le i (Array_size_inst1 A xs)) (default : A) :
 standard_bool (Array_isEqvAux_inst1 A xs ys hsz p i hi) = true <->
 forall n, n < nat_of_Nat i -> nth n (array_values xs) default = nth n (array_values ys) default.
Proof.
 revert hi; induction i as [|i IH]; intro hi.
 - change (true = true <-> forall n, n < 0 -> nth n (array_values xs) default = nth n (array_values ys) default); split; intros; try reflexivity; lia.
 - assert (hy : Nat_le (Nat_succ i) (Array_size_inst1 A ys)).
   { pose proof (imported_equality_standard _ _ _ hsz) as E. rewrite <- E; exact hi. }
   assert (hp : Nat_le i (Array_size_inst1 A xs)).
   { apply nat_le_Nat_le; pose proof (Nat_le_nat_le' _ _ hi); cbn [nat_of_Nat] in H; lia. }
   change (standard_bool (Bool_and
     (p (Array_getInternal_inst1 A xs i hi) (Array_getInternal_inst1 A ys i hy))
     (Array_isEqvAux_inst1 A xs ys hsz p i hp)) = true <->
     forall n, n < S (nat_of_Nat i) -> nth n (array_values xs) default = nth n (array_values ys) default).
   rewrite standard_bool_and, andb_true_iff, GOOD, (IH hp).
   rewrite !(array_get_exact _ _ _ _ default).
   split.
   + intros [LAST BEFORE] n LT; destruct (Nat.eq_dec n (nat_of_Nat i)); [subst;exact LAST|apply BEFORE;lia].
   + intro ALL; split; [apply ALL;lia|intros n LT;apply ALL;lia].
Qed.
Lemma array_eq_exact A (xs ys : Array_inst1 A) (p : A -> A -> Bool)
 (GOOD : forall a b, standard_bool (p a b) = true <-> a = b) (default : A) :
 standard_bool (Array_isEqv_inst1 A xs ys p) = true <-> array_values xs = array_values ys.
Proof.
 unfold Array_isEqv_inst1.
 destruct (Nat.eq_dec (length (array_values xs)) (length (array_values ys))) as [SAME|DIFF].
 - assert (H : Lean.eq (Array_size_inst1 A xs) (Array_size_inst1 A ys)).
   { apply standard_equality_imported.
     rewrite <- (Nat2natid (Array_size_inst1 A xs)), <- (Nat2natid (Array_size_inst1 A ys)).
     now rewrite !array_size_exact, SAME. }
   rewrite (imported_dite_true _ _ _ _ _ H).
   rewrite (array_eq_aux_exact A xs ys H p GOOD _ _ default), array_size_exact.
   split.
   + intro ALL; apply nth_ext with (d:=default) (d':=default); assumption.
   + intros E n LT; now rewrite E.
 - assert (H : Not (Lean.eq (Array_size_inst1 A xs) (Array_size_inst1 A ys))).
   { intro E; apply imported_equality_standard in E.
     apply (f_equal nat_of_Nat) in E; rewrite !array_size_exact in E; exfalso; contradiction. }
   rewrite (imported_dite_false _ _ _ _ _ H).
   change (false = true <-> array_values xs = array_values ys).
   split; [discriminate|intro E;apply (f_equal (@length A)) in E;contradiction].
Qed.
