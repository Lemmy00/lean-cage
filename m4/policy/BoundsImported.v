(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Imported live-policy interface agrees with native rejection. *)
From Stdlib Require Import ZArith List Lia Bool.
From LeanImport Require Import Lean.
From LeanCageBounds Require Import BoundsImport BoundsImportedValues BoundsPredicate.
Local Close Scope lean_scope.
Open Scope Z_scope.
Lemma bound_decide_le a b :
 bound_bool(Decidable_decide(LE_le_inst1 Nat instLENat a b)(Nat_decLe a b))=
 (bound_nat a<=?bound_nat b).
Proof. apply bound_ble. Qed.
Lemma bound_decide_eq a b :
 bound_bool(BEq_beq_inst1 Nat(instBEqOfDecidableEq_inst1 Nat instDecidableEqNat)a b)=
 (bound_nat a=?bound_nat b).
Proof. apply bound_beq. Qed.
Ltac bound_literals :=
 cbv beta iota zeta delta[OfNat_ofNat_inst1 instOfNatNat ofNat0] in *;
 repeat first[rewrite bound_nat_double|rewrite bound_nat_succ|rewrite bound_nat_zero].
Theorem imported_numeric_limits fields : length(bound_values fields)=10%nat ->
 bound_bool(LeanCageM4_Bounds_nativeLimits fields)=numeric_limits(bound_values fields).
Proof.
 intros LEN;unfold LeanCageM4_Bounds_nativeLimits.
 rewrite !bound_bool_and,!bound_decide_le,!bound_decide_eq,!imported_page_aligned.
 rewrite imported_field_count,LEN;bound_literals.
 rewrite !imported_field_at.
 unfold numeric_limits;reflexivity.
Qed.
Theorem imported_argument_bounds argc bytes : 16<=bound_nat argc ->
 bound_bool(LeanCageM4_Bounds_nativeArguments argc bytes)=
 (bound_nat argc-16<=?64)&&(bound_nat bytes<=?16384).
Proof.
 intros COUNT;unfold LeanCageM4_Bounds_nativeArguments.
 rewrite bound_bool_and,!bound_decide_le.
 change(bound_nat(HSub_hSub_inst7 Nat Nat Nat(instHSub_inst1 Nat instSubNat)argc 16%Nat))
 with(bound_nat(BoundsImport.Nat_sub argc 16)).
 rewrite bound_sub;bound_literals;rewrite Z.max_r by lia;reflexivity.
Qed.
Theorem imported_bounds_exact argc bytes fields : 16<=bound_nat argc ->
 length(bound_values fields)=10%nat ->
 bound_bool(LeanCageM4_Bounds_nativeBounds argc bytes fields)=
 negb(BoundsStructure.bounds_rejected(bound_nat argc)(bound_nat bytes)(bound_values fields)).
Proof.
 intros COUNT LEN;unfold LeanCageM4_Bounds_nativeBounds;rewrite bound_bool_and,
 imported_argument_bounds by exact COUNT;rewrite imported_numeric_limits by exact LEN.
 symmetry;apply bounds_predicate_exact.
Qed.
