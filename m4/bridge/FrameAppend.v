(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import Arith List Lia.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat FrameLists FrameArray.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Import ListNotations.

Definition append_loop A (a : Array_inst1 A) i j (bs : Array_inst1 A) :=
 Array_foldlM_loop_inst7 A (Array_inst1 A) Id_inst1 Id_instMonad_inst1
   (Array_push_inst1 A) a (Array_size_inst1 A a) (Array_isEqv__proof_1_inst1 A a) i j bs.
Lemma append_loop_extract A (a : Array_inst1 A) i j bs :
 append_loop A a i j bs = Array_extract_loop_inst1 A a i j bs.
Proof.
 revert j bs; induction i as [|i IH]; intros j bs.
 - reflexivity.
 - change (dite _ _ (Nat_decLt j (Array_size_inst1 A a))
     (fun h => append_loop A a i (Nat_succ j)
       (Array_push_inst1 A bs (Array_getInternal_inst1 A a j h))) (fun _ => bs) =
     dite _ _ (Nat_decLt j (Array_size_inst1 A a))
     (fun h => Array_extract_loop_inst1 A a i (Nat_succ j)
       (Array_push_inst1 A bs (Array_getInternal_inst1 A a j h))) (fun _ => bs)).
   destruct (Nat_decLt j (Array_size_inst1 A a)) as [b h]; destruct b; [reflexivity|].
   apply IH.
Qed.
Lemma array_append_exact A (a b : Array_inst1 A) (default : A) :
 array_values (Array_append_inst1 A a b) = array_values a ++ array_values b.
Proof.
 unfold Array_append_inst1, Array_foldl_inst3, Array_foldlM_inst7.
 rewrite (imported_dite_true _ _ _ _ _ (Array_isEqv__proof_1_inst1 A b)).
 change (array_values (append_loop A b (Array_size_inst1 A b) Nat_zero a) =
   array_values a ++ array_values b).
 rewrite append_loop_extract, (array_extract_loop_exact A b a _ _ default).
 rewrite array_size_exact; cbn [nat_of_Nat skipn]; now rewrite firstn_all.
Qed.
Lemma array_values_injective A (a b : Array_inst1 A) : array_values a = array_values b -> a = b.
Proof.
 destruct a as [a], b as [b]; intro H.
 change (standard_list a = standard_list b) in H.
 apply (f_equal (@imported_list A)) in H.
 now rewrite !imported_standard_list in H; subst.
Qed.
