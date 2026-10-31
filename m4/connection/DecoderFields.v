(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Actual typed field reads from the constructed result object. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Errors Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps StoreSteps LocalAccess ScalarMemory ResultLayout ResultSource
  FrameBytes DecoderLayout DecoderSource.
Import ListNotations.
Open Scope Z_scope.

Theorem decoded_cell_loadv : forall m output ofs bytes cell,
  0 <= ofs -> ofs+144 <= Ptrofs.modulus ->
  decoded_contents m output ofs bytes -> In cell (decoded_cells bytes) ->
  Mem.loadv (scalar_chunk cell) m
    (Vptr output (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr (scalar_offset cell)))) =
    Some (Val.load_result (scalar_chunk cell) (scalar_value cell)).
Proof.
  intros m output ofs bytes cell LOW HIGH CONTENT IN.
  pose proof (decoded_cells_valid bytes) as VALID. rewrite Forall_forall in VALID.
  destruct (VALID cell IN) as [START [END ALIGN]].
  pose proof (size_chunk_pos (scalar_chunk cell)) as POS.
  rewrite pointer_add_representations. unfold Mem.loadv.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned;lia).
  destruct (zle (ofs+scalar_offset cell+size_chunk (scalar_chunk cell)) Ptrofs.modulus);
    [apply CONTENT;exact IN|lia].
Qed.

Theorem decoder_field_value : forall m local le output ofs bytes field ty cell,
  le ! _r = Some (Vptr output (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs+144 <= Ptrofs.modulus -> decoded_contents m output ofs bytes ->
  In cell (decoded_cells bytes) -> access_mode ty = By_value (scalar_chunk cell) ->
  field_offset result_ge field result_members = OK (scalar_offset cell,Full) ->
  expression_value result_ge (decoder_env local) le m
    (Efield (Ederef (Etempvar _r (tptr result_type)) result_type) field ty)
    (Val.load_result (scalar_chunk cell) (scalar_value cell)).
Proof.
  intros m local le output ofs bytes field ty cell REG LOW HIGH CONTENT IN MODE FIELD.
  eapply location_read_value.
  - eapply struct_location_value with (delta := scalar_offset cell).
    + eapply location_read_value.
      * eapply pointer_location_value. apply old_expression_value.
        apply value_temp; exact REG.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + reflexivity.
    + exact FIELD.
  - eapply deref_loc_value; [exact MODE|]. eapply decoded_cell_loadv; eassumption.
Qed.

Ltac decoder_field_cell bytes field := lazymatch field with
  | _kind => constr:(cell32 0 (byte_word_at bytes 6))
  | _stage => constr:(cell32 4 (word32_at bytes 32))
  | _detail => constr:(cell32 8 (word32_at bytes 36))
  | _entry => constr:(cell32 12 (word32_at bytes 40))
  | _clean => constr:(cell32 16 (word32_at bytes 44))
  | _triggers => constr:(cell32 20 (word32_at bytes 48))
  | _uid => constr:(cell32 24 (word32_at bytes 52))
  | _run => constr:(cell64 32 (word64_at bytes 8))
  | _cpu => constr:(cell64 40 (word64_at bytes 56))
  | _peak => constr:(cell64 48 (word64_at bytes 64))
  | _out => constr:(cell64 56 (word64_at bytes 72))
  | _err => constr:(cell64 64 (word64_at bytes 80))
  | _elapsed => constr:(cell64 72 (word64_at bytes 88))
  end.
