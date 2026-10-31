(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.input: Distinct source result fields and the complete outgoing frame bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
Require Import Slice Library ScalarMemory ResultLayout Writers DecoderValidity.
Import ListNotations.
Open Scope Z_scope.
Record frame_result := {
  fr_kind : int; fr_stage : int; fr_detail : int; fr_entry : int;
  fr_clean : int; fr_triggers : int; fr_uid : int; fr_run : int64;
  fr_cpu : int64; fr_peak : int64; fr_out : int64; fr_err : int64; fr_elapsed : int64;
  fr_oom : int64; fr_pids : int64; fr_export_state : int; fr_omitted : int; fr_export_error : int
}.
Definition frame_digest_cell digest index :=
  {|scalar_chunk:=Mint8unsigned;scalar_offset:=108+Z.of_nat index;
    scalar_value:=Vint (Int.repr (Byte.unsigned (nth index digest Byte.zero)))|}.
Definition frame_result_cells r digest :=
  [cell32 0 (fr_kind r);cell32 4 (fr_stage r);cell32 8 (fr_detail r);cell32 12 (fr_entry r);
   cell32 16 (fr_clean r);cell32 20 (fr_triggers r);cell32 24 (fr_uid r);cell64 32 (fr_run r);
   cell64 40 (fr_cpu r);cell64 48 (fr_peak r);cell64 56 (fr_out r);cell64 64 (fr_err r);
   cell64 72 (fr_elapsed r);cell64 80 (fr_oom r);cell64 88 (fr_pids r);
   cell32 96 (fr_export_state r);cell32 100 (fr_omitted r);cell32 104 (fr_export_error r)] ++
   map (frame_digest_cell digest) (seq 0 32).
Definition frame_result_contents m b ofs r digest :=
  forall cell, In cell (frame_result_cells r digest) ->
    Mem.load (scalar_chunk cell) m b (ofs+scalar_offset cell)=
      Some (Val.load_result (scalar_chunk cell) (scalar_value cell)).
Definition frame_result_owned m b ofs r digest :=
  0<=ofs /\ ofs+144<=Ptrofs.modulus /\ (8|ofs) /\
  Mem.range_perm m b ofs (ofs+144) Cur Readable /\ length digest=32%nat /\
  frame_result_contents m b ofs r digest /\
  readable_bytes m {|address_block:=b;address_offset:=ofs+108|} digest.
Theorem frame_result_cells_valid : forall r digest,
  Forall (scalar_valid 144) (frame_result_cells r digest).
Proof. intros;apply scalar_list_validb_sound;reflexivity. Qed.
Theorem frame_result_cells_separate : forall r digest before cell rest,
  frame_result_cells r digest=before++cell::rest -> Forall (scalar_separate cell) rest.
Proof. intros;eapply (scalar_orderedb_sound (frame_result_cells r digest));[reflexivity|exact H]. Qed.
Definition frame_word32 x := map (fun word => Byte.repr (Int.unsigned word)) (put32_values x).
Definition frame_word64 x := map (fun word => Byte.repr (Int.unsigned word)) (put64_values x).
Definition outgoing_frame sequence r digest :=
  frame_magic ++ [Byte.repr 1;Byte.zero;Byte.repr (Int.unsigned (fr_kind r));Byte.zero] ++
  frame_word64 (fr_run r) ++ frame_word64 sequence ++ frame_word32 (Int.repr 128) ++ repeat Byte.zero 4 ++
  frame_word32 (fr_stage r) ++ frame_word32 (fr_detail r) ++ frame_word32 (fr_entry r) ++
  frame_word32 (fr_clean r) ++ frame_word32 (fr_triggers r) ++ frame_word32 (fr_uid r) ++
  frame_word64 (fr_cpu r) ++ frame_word64 (fr_peak r) ++ frame_word64 (fr_out r) ++
  frame_word64 (fr_err r) ++ frame_word64 (fr_elapsed r) ++
  frame_word32 (fr_export_state r) ++ frame_word32 (fr_omitted r) ++ digest ++
  frame_word64 (fr_oom r) ++ frame_word64 (fr_pids r) ++ frame_word32 (fr_export_error r) ++ repeat Byte.zero 4.
Lemma frame_word32_length : forall x,length (frame_word32 x)=4%nat.
Proof. reflexivity. Qed.
Lemma frame_word64_length : forall x,length (frame_word64 x)=8%nat.
Proof. reflexivity. Qed.
Theorem outgoing_frame_length : forall sequence r digest,
  length digest=32%nat -> length (outgoing_frame sequence r digest)=160%nat.
Proof.
  intros;unfold outgoing_frame;repeat rewrite app_length;
    rewrite !frame_word32_length,!frame_word64_length,!repeat_length,H;reflexivity.
Qed.
