(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Connect successful native numeric reads to the actual worker byte decoder. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import Machine ArgumentsImport ArgumentConnection ArgumentValues.
From EntryNative Require Import EntrySource NativeArguments.
From LeanCageMainNumber Require Import NumberMath NumberMemory.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Definition argument_byte (b : Byte.int) : UInt8.
Proof.
  refine (UInt8_ofBitVec (BitVec_ofFin _ (Fin_mk _ (Nat_of_nat (Z.to_nat (Byte.unsigned b))) _))).
  change (Nat_le (Nat_of_nat (S (Z.to_nat (Byte.unsigned b)))) (Nat_of_nat 256)).
  apply nat_le_Nat_le; rewrite !nat2Natid.
  pose proof (Byte.unsigned_range b); change (0 <= Byte.unsigned b < 256) in H; lia.
Defined.

Lemma argument_byte_exact b :
  nat_of_Nat (UInt8_toNat (argument_byte b)) = Z.to_nat (Byte.unsigned b).
Proof. apply nat2Natid. Qed.

Fixpoint argument_bytes (bytes : list Byte.int) : List_inst1 UInt8 :=
  match bytes with
  | [] => List_nil_inst1 UInt8
  | byte :: rest => List_cons_inst1 UInt8 (argument_byte byte) (argument_bytes rest)
  end.

Theorem argument_fold_native bytes initial :
  Forall decimal_digit_ok bytes ->
  Z.of_nat (argument_fold initial (argument_bytes bytes)) = decimal_fold (Z.of_nat initial) bytes.
Proof.
  revert initial; induction bytes as [|byte rest IH]; intros initial DIGITS; [reflexivity|].
  inversion DIGITS as [|? ? DIG TAIL]; subst.
  cbn [argument_fold argument_bytes decimal_fold].
  rewrite IH by exact TAIL.
  rewrite argument_byte_exact.
  f_equal.
  unfold decimal_digit_ok in DIG; unfold decimal_digit.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_sub by lia.
  rewrite Z2Nat.id by lia; lia.
Qed.

(* The caller must still produce these two executions on the same owned bytes. *)
Theorem current_number_worker_value cell before input offset bytes output outoffset events after limit decoded :
  number_input before input offset bytes -> number_output before output outoffset ->
  steps (Clight.globalenv EntrySource.prog) cell
    (live (Callstate (Ctypes.Internal EntrySource.f_number)
      [Vptr input offset; Vptr output outoffset] Kstop before)) events
    (live (Returnstate (Vint Int.zero) Kstop after)) ->
  Lean.eq (LeanCage_Entry_Arguments_unsigned limit (argument_bytes bytes)) (Option_some_inst1 Lean.Nat decoded) ->
  Mem.loadv Mint64 after (Vptr output outoffset) =
    Some (Vlong (Int64.repr (Z.of_nat (nat_of_Nat decoded)))).
Proof.
  intros INPUT OUTPUT RUN DECODED.
  destruct (current_entry_number_value _ _ _ _ _ _ _ _ _ INPUT OUTPUT RUN)
    as [value [PARSED [DIGITS [RANGE [VALUE LOAD]]]]].
  rewrite (argument_unsigned_value _ _ _ DECODED), argument_fold_native by exact DIGITS.
  change (Mem.loadv Mint64 after (Vptr output outoffset) =
    Some (Vlong (Int64.repr (decimal_fold 0 bytes)))).
  rewrite <- VALUE; exact LOAD.
Qed.
