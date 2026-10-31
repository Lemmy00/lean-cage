(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Output fields written before the private decoder's later checks. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
Require Import Slice ScalarMemory ResultLayout FrameBytes.
Import ListNotations.
Open Scope Z_scope.

Definition decoded_cells bytes :=
  [cell32 0 (byte_word_at bytes 6); cell32 4 (word32_at bytes 32);
   cell32 8 (word32_at bytes 36); cell32 12 (word32_at bytes 40);
   cell32 16 (word32_at bytes 44); cell32 20 (word32_at bytes 48);
   cell32 24 (word32_at bytes 52); cell64 32 (word64_at bytes 8);
   cell64 40 (word64_at bytes 56); cell64 48 (word64_at bytes 64);
   cell64 56 (word64_at bytes 72); cell64 64 (word64_at bytes 80);
   cell64 72 (word64_at bytes 88); cell64 80 Int64.zero; cell64 88 Int64.zero;
   cell32 96 Int.zero; cell32 100 Int.zero; cell32 104 Int.zero] ++ map digest_cell (seq 0 32).
Definition decoded_contents m b ofs bytes := forall cell,
  In cell (decoded_cells bytes) ->
  Mem.load (scalar_chunk cell) m b (ofs+scalar_offset cell) =
    Some (Val.load_result (scalar_chunk cell) (scalar_value cell)).

Theorem decoded_cells_valid : forall bytes, Forall (scalar_valid 144) (decoded_cells bytes).
Proof. intros; apply scalar_list_validb_sound; reflexivity. Qed.
Theorem decoded_cells_separate : forall bytes before cell rest,
  decoded_cells bytes = before ++ cell::rest -> Forall (scalar_separate cell) rest.
Proof. intros; eapply (scalar_orderedb_sound (decoded_cells bytes)); [reflexivity|eassumption]. Qed.
Theorem decoded_cells_destination_alignment : forall bytes ofs cell,
  (8 | ofs) -> In cell (decoded_cells bytes) ->
  (align_chunk (scalar_chunk cell) | ofs+scalar_offset cell).
Proof.
  intros bytes ofs cell [factor EQ] IN. unfold decoded_cells in IN; cbn in IN.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction; subst cell;
    cbn; rewrite EQ.
  all: cbv [Archi.align_int64].
  all: apply Z.divide_add_r.
  all: try (apply Z.mod_divide; [lia|reflexivity]).
  all: apply Z.divide_mul_r; apply Z.mod_divide; [lia|reflexivity].
Qed.
Theorem decoded_cells_complete : forall initial local bytes after,
  scalar_stores local initial (decoded_cells bytes) after -> decoded_contents after local 0 bytes.
Proof.
  intros initial local bytes after RUN cell IN; cbn.
  eapply scalar_stores_fields; [exact RUN|intros; eapply decoded_cells_separate; eassumption|exact IN].
Qed.
Theorem decoded_struct_copy_fields : forall m after local output ofs values bytes,
  decoded_contents m local 0 bytes -> (8 | ofs) ->
  Mem.loadbytes m local 0 144 = Some values -> Mem.storebytes m output ofs values = Some after ->
  decoded_contents after output ofs bytes.
Proof.
  intros m after local output ofs values bytes CONTENT ALIGN LOAD STORE cell IN.
  pose proof (Mem.loadbytes_length _ _ _ _ _ LOAD) as LENGTH.
  assert (LEN : Z.of_nat (length values) = 144) by (rewrite LENGTH; reflexivity).
  pose proof (decoded_cells_valid bytes) as VALID.
  rewrite Forall_forall in VALID. destruct (VALID cell IN) as [LOW [HIGH ALIGNED]].
  eapply copied_scalar_load with (src := local) (sofs := 0) (bytes := values).
  - rewrite LEN; exact LOAD.
  - exact STORE.
  - exact LOW.
  - rewrite LEN; exact HIGH.
  - eapply decoded_cells_destination_alignment; eassumption.
  - apply CONTENT; exact IN.
Qed.
