(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.bytes: Explicit imported values connected to actual source executions. *)
From Stdlib Require Import Arith List Lia.
From LeanImport Require Import Lean.
Require Import NormalizedImport.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Lemma imported_add_exact a b :
  nat_of_Nat (Nat_add a b) = nat_of_Nat a + nat_of_Nat b.
Proof.
  induction b as [|b IH].
  - change (nat_of_Nat a = nat_of_Nat a + 0); lia.
  - change (S (nat_of_Nat (Nat_add a b)) = nat_of_Nat a + S (nat_of_Nat b)).
    rewrite IH; lia.
Qed.
Lemma imported_mul_exact a b :
  nat_of_Nat (Nat_mul a b) = nat_of_Nat a * nat_of_Nat b.
Proof.
  induction b as [|b IH].
  - change (0 = nat_of_Nat a * 0); lia.
  - change (nat_of_Nat (Nat_add (Nat_mul a b) a) = nat_of_Nat a * S (nat_of_Nat b)).
    rewrite imported_add_exact, IH; lia.
Qed.
Lemma imported_pow_exact a b :
  nat_of_Nat (Nat_pow a b) = Nat.pow (nat_of_Nat a) (nat_of_Nat b).
Proof.
  induction b as [|b IH].
  - reflexivity.
  - change (nat_of_Nat (Nat_mul (Nat_pow a b) a) = nat_of_Nat a * Nat.pow (nat_of_Nat a) (nat_of_Nat b)).
    rewrite imported_mul_exact, IH; lia.
Qed.

Fixpoint standard_list {A : Type} (xs : List_inst1 A) : list A :=
  match xs with List_nil_inst1 _ => nil | List_cons_inst1 _ x xs => cons x (standard_list xs) end.
Fixpoint imported_list {A : Type} (xs : list A) : List_inst1 A :=
  match xs with nil => List_nil_inst1 A | cons x xs => List_cons_inst1 A x (imported_list xs) end.
Lemma standard_imported_list A (xs : list A) : standard_list (imported_list xs) = xs.
Proof. induction xs; simpl; congruence. Qed.
Lemma imported_standard_list A (xs : List_inst1 A) : imported_list (standard_list xs) = xs.
Proof. induction xs; simpl; congruence. Qed.

Lemma imported_lookup_exact xs i :
 nat_of_Nat (UInt8_toNat (LeanCageM4_Normalized_lookup xs i)) =
 nth (nat_of_Nat i) (List.map (fun b : UInt8 => nat_of_Nat (UInt8_toNat b)) (standard_list xs)) 0.
Proof.
 revert i; induction xs as [|b bs IH]; intros i; destruct i as [|i].
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - change (nat_of_Nat (UInt8_toNat (LeanCageM4_Normalized_lookup bs i)) =
   nth (nat_of_Nat i) (List.map (fun b : UInt8 => nat_of_Nat (UInt8_toNat b)) (standard_list bs)) 0).
   apply IH.
Qed.

Lemma imported_foldl_nats f g
 (STEP : forall a b, nat_of_Nat (f a b) = g (nat_of_Nat a) (nat_of_Nat b)) xs init :
 nat_of_Nat (List_foldl_inst3 Nat Nat f init xs) =
 List.fold_left g (List.map nat_of_Nat (standard_list xs)) (nat_of_Nat init).
Proof.
 revert init; induction xs as [|x xs IH]; intro init.
 - reflexivity.
 - change (nat_of_Nat (List_foldl_inst3 Nat Nat f (f init x) xs) =
     List.fold_left g (List.map nat_of_Nat (standard_list xs)) (g (nat_of_Nat init) (nat_of_Nat x))).
   rewrite IH, STEP; reflexivity.
Qed.
Lemma imported_range_loop_exact n acc :
 List.map nat_of_Nat (standard_list (List_range_loop n acc)) =
 List.seq 0 (nat_of_Nat n) ++ List.map nat_of_Nat (standard_list acc).
Proof.
 revert acc; induction n as [|n IH]; intro acc.
 - reflexivity.
 - change (List.map nat_of_Nat (standard_list (List_range_loop n (List_cons_inst1 Nat n acc))) =
     List.seq 0 (S (nat_of_Nat n)) ++ List.map nat_of_Nat (standard_list acc)).
   rewrite IH, List.seq_S. cbn [standard_list List.map Nat.add].
   rewrite <- List.app_assoc; reflexivity.
Qed.
Lemma imported_range_exact n :
 List.map nat_of_Nat (standard_list (List_range n)) = List.seq 0 (nat_of_Nat n).
Proof. unfold List_range; rewrite imported_range_loop_exact; apply List.app_nil_r. Qed.

Definition byte_values bytes :=
 List.map (fun b : UInt8 => nat_of_Nat (UInt8_toNat b))
   (standard_list (Array_toList_inst1 UInt8 (ByteArray_data bytes))).
Lemma imported_byteAt_exact bytes i :
 nat_of_Nat (UInt8_toNat (LeanCageM4_Normalized_byteAt bytes i)) =
 nth (nat_of_Nat i) (byte_values bytes) 0.
Proof. apply imported_lookup_exact. Qed.

Definition natural_little (bytes : list nat) (offset width : nat) : nat :=
 List.fold_left (fun n i => n + nth (offset + i) bytes 0 * Nat.pow 2 (8*i))
   (List.seq 0 width) 0.
Theorem imported_little_exact bytes offset width :
 nat_of_Nat (LeanCageM4_Normalized_littleBytes bytes offset width) =
 natural_little (byte_values bytes) (nat_of_Nat offset) (nat_of_Nat width).
Proof.
 unfold LeanCageM4_Normalized_littleBytes.
 transitivity (List.fold_left
   (fun n i => n + nth (nat_of_Nat offset+i) (byte_values bytes) 0 * Nat.pow 2 (8*i))
   (List.map nat_of_Nat (standard_list (List_range width))) 0).
 - apply imported_foldl_nats. intros a b.
   change (nat_of_Nat (Nat_add a (Nat_mul
      (UInt8_toNat (LeanCageM4_Normalized_byteAt bytes (Nat_add offset b)))
      (Nat_pow 2 (Nat_mul 8 b)))) =
      nat_of_Nat a + nth (nat_of_Nat offset + nat_of_Nat b) (byte_values bytes) 0 *
        Nat.pow 2 (8 * nat_of_Nat b)).
   rewrite imported_add_exact, imported_mul_exact, imported_byteAt_exact,
     imported_add_exact, imported_pow_exact, imported_mul_exact.
   reflexivity.
 - rewrite imported_range_exact; reflexivity.
Qed.
