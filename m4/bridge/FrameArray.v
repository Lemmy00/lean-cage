(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import Arith List Lia.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat FrameLists.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Import ListNotations.

Definition array_values {A : Type} (a : Array_inst1 A) := standard_list (Array_toList_inst1 A a).
Lemma array_size_exact A (a : Array_inst1 A) :
 nat_of_Nat (Array_size_inst1 A a) = length (array_values a).
Proof. apply imported_length_exact. Qed.
Lemma array_push_exact A (a : Array_inst1 A) x :
 array_values (Array_push_inst1 A a x) = array_values a ++ [x].
Proof. apply imported_concat_exact. Qed.
Lemma array_get_exact A (a : Array_inst1 A) i h (default : A) :
 Array_getInternal_inst1 A a i h = nth (nat_of_Nat i) (array_values a) default.
Proof. apply imported_get_exact. Qed.

Lemma extract_loop_zero A (a bs : Array_inst1 A) j :
 Array_extract_loop_inst1 A a Nat_zero j bs = bs.
Proof.
 change (dite _ _ (Nat_decLt j (Array_size_inst1 A a)) (fun _ => bs) (fun _ => bs) = bs).
 destruct (Nat_decLt j (Array_size_inst1 A a)) as [b h]; destruct b; reflexivity.
Qed.
Lemma extract_loop_succ A (a bs : Array_inst1 A) i j
 (h : Nat_le (Nat_succ j) (Array_size_inst1 A a)) :
 Array_extract_loop_inst1 A a (Nat_succ i) j bs =
 Array_extract_loop_inst1 A a i (Nat_succ j)
   (Array_push_inst1 A bs (Array_getInternal_inst1 A a j h)).
Proof.
 change (dite _ _ (Nat_decLt j (Array_size_inst1 A a))
   (fun h => Array_extract_loop_inst1 A a i (Nat_succ j)
     (Array_push_inst1 A bs (Array_getInternal_inst1 A a j h))) (fun _ => bs) =
   Array_extract_loop_inst1 A a i (Nat_succ j)
     (Array_push_inst1 A bs (Array_getInternal_inst1 A a j h))).
 exact (imported_dite_true _ _ _ _ _ h).
Qed.
Lemma extract_loop_outside A (a bs : Array_inst1 A) i j
 (h : Not (Nat_le (Nat_succ j) (Array_size_inst1 A a))) :
 Array_extract_loop_inst1 A a i j bs = bs.
Proof.
 destruct i as [|i]; [apply extract_loop_zero|].
 change (dite _ _ (Nat_decLt j (Array_size_inst1 A a))
   (fun h => Array_extract_loop_inst1 A a i (Nat_succ j)
     (Array_push_inst1 A bs (Array_getInternal_inst1 A a j h))) (fun _ => bs) = bs).
 exact (imported_dite_false _ _ _ _ _ h).
Qed.
Lemma skipn_nth A (xs : list A) n (default : A) : n < length xs ->
 skipn n xs = nth n xs default :: skipn (S n) xs.
Proof.
 revert xs; induction n as [|n IH]; intros [|x xs] H; simpl in *; try lia; try reflexivity.
 apply IH; lia.
Qed.
Lemma array_extract_loop_exact A (a bs : Array_inst1 A) i j (default : A) :
 array_values (Array_extract_loop_inst1 A a i j bs) =
 array_values bs ++ firstn (nat_of_Nat i) (skipn (nat_of_Nat j) (array_values a)).
Proof.
 revert j bs; induction i as [|i IH]; intros j bs.
 - rewrite extract_loop_zero; simpl; now rewrite app_nil_r.
 - destruct (le_dec (S (nat_of_Nat j)) (length (array_values a))) as [LT|GE].
   + assert (h : Nat_le (Nat_succ j) (Array_size_inst1 A a)).
     { apply nat_le_Nat_le; rewrite array_size_exact; exact LT. }
     rewrite (extract_loop_succ A a bs i j h), IH, array_push_exact.
     rewrite (array_get_exact A a j h default).
     rewrite (skipn_nth A (array_values a) (nat_of_Nat j) default ltac:(lia)).
     cbn [nat_of_Nat firstn]; rewrite <- app_assoc; reflexivity.
   + assert (h : Not (Nat_le (Nat_succ j) (Array_size_inst1 A a))).
     { apply imported_not_le; rewrite array_size_exact; simpl; lia. }
     rewrite (extract_loop_outside A a bs (Nat_succ i) j h).
     rewrite skipn_all2 by lia; rewrite firstn_nil, app_nil_r; reflexivity.
Qed.
Lemma array_extract_exact A (a : Array_inst1 A) start stop (default : A) :
 array_values (Array_extract_inst1 A a start stop) =
 firstn (nat_of_Nat stop - nat_of_Nat start) (skipn (nat_of_Nat start) (array_values a)).
Proof.
 unfold Array_extract_inst1.
 rewrite (array_extract_loop_exact A a _ _ _ default).
 change ([] ++ firstn
   (nat_of_Nat (Nat_sub (Min_min_inst1 Nat instMinNat stop (Array_size_inst1 A a)) start))
   (skipn (nat_of_Nat start) (array_values a)) =
   firstn (nat_of_Nat stop - nat_of_Nat start) (skipn (nat_of_Nat start) (array_values a))).
 rewrite imported_sub_exact, imported_min_exact, array_size_exact.
 rewrite <- Nat.sub_min_distr_r, <- firstn_firstn, <- length_skipn, firstn_all.
 reflexivity.
Qed.
