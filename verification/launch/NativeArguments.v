(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Reuse numeric source semantics in the actual production handoff program. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Machine.
From EntryNative Require Import EntrySource.
From LeanCageMain Require Import Main.
From LeanCageMainNumber Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource.
Import ListNotations.
Open Scope Z_scope.

Theorem current_entry_number_exact : EntrySource.f_number = Main.f_number.
Proof. reflexivity. Qed.

(* This starts at the actual number call. The surrounding guest/caller producer is still required. *)
Theorem current_entry_number_value cell before input offset bytes output outoffset events after :
  number_input before input offset bytes -> number_output before output outoffset ->
  steps (Clight.globalenv EntrySource.prog) cell
    (live (Callstate (Internal EntrySource.f_number)
      [Vptr input offset; Vptr output outoffset] Kstop before)) events
    (live (Returnstate (Vint Int.zero) Kstop after)) ->
  exists value,
    decimal_number bytes = Some value /\
    Forall decimal_digit_ok bytes /\ 0 <= value <= Int64.max_unsigned /\
    value = decimal_fold 0 bytes /\
    Mem.loadv Mint64 after (Vptr output outoffset) = Some (Vlong (Int64.repr value)).
Proof.
  intros INPUT OUTPUT RUN.
  rewrite current_entry_number_exact in RUN.
  change (steps (Clight.globalenv EntrySource.prog) cell
    (live (number_initial (Vptr input offset) (Vptr output outoffset) Kstop before)) events
    (live (Returnstate (Vint Int.zero) Kstop after))) in RUN.
  destruct (number_source_return _ _ _ _ _ _ _ _ _ _ _ INPUT OUTPUT RUN) as [CODE POST].
  destruct (decimal_number bytes) as [value|] eqn:PARSED.
  - exists value; split; [reflexivity|].
    destruct (proj1 (decimal_number_exact bytes value) PARSED) as [_ [DIGITS [VALUE RANGE]]].
    split; [exact DIGITS|]. split; [exact RANGE|]. split; [exact VALUE|].
    unfold number_post in POST.
    unfold Mem.storev in POST; unfold Mem.loadv.
    destruct (zle (Ptrofs.unsigned outoffset + size_chunk Mint64) Ptrofs.modulus).
    + rewrite (Mem.load_store_same _ _ _ _ _ _ POST); reflexivity.
    + discriminate POST.
  - discriminate CODE.
Qed.
