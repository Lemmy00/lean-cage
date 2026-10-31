(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-structures.result: Distinct actual struct layout and wire layout. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Errors Ctypes Ctypesdefs Clight.
Require Import Slice ScalarMemory.
Import ListNotations.
Open Scope Z_scope.
Definition result_type := Tstruct _result noattr.
Definition result_ge := Clight.globalenv Slice.prog.
Definition result_members := match (genv_cenv result_ge) ! _result with Some co => co_members co | None => [] end.
Definition cell32 ofs value := {|scalar_chunk := Mint32; scalar_offset := ofs; scalar_value := Vint value|}.
Definition cell64 ofs value := {|scalar_chunk := Mint64; scalar_offset := ofs; scalar_value := Vlong value|}.
Definition digest_cell index := {|scalar_chunk := Mint8unsigned; scalar_offset := 108 + Z.of_nat index; scalar_value := Vint Int.zero|}.
Definition result_cells kind stage detail entry uid run :=
  [cell32 0 kind; cell32 4 stage; cell32 8 detail; cell32 12 entry;
   cell32 16 Int.zero; cell32 20 Int.zero; cell32 24 uid; cell64 32 run;
   cell64 40 Int64.zero; cell64 48 Int64.zero; cell64 56 Int64.zero; cell64 64 Int64.zero;
   cell64 72 Int64.zero; cell64 80 Int64.zero; cell64 88 Int64.zero;
   cell32 96 Int.zero; cell32 100 Int.zero; cell32 104 Int.zero] ++ map digest_cell (seq 0 32).
Definition result_contents m b ofs kind stage detail entry uid run :=
  forall cell, In cell (result_cells kind stage detail entry uid run) ->
  Mem.load (scalar_chunk cell) m b (ofs+scalar_offset cell) =
    Some (Val.load_result (scalar_chunk cell) (scalar_value cell)).
Definition result_destination m b ofs :=
  0 <= ofs /\ ofs+144 <= Ptrofs.modulus /\ (8 | ofs) /\
  Mem.range_perm m b ofs (ofs+144) Cur Writable.

Theorem result_abi_layout :
  sizeof result_ge result_type = 144 /\ alignof result_ge result_type = 8 /\
  map (fun id => field_offset result_ge id result_members)
    [_kind;_stage;_detail;_entry;_clean;_triggers;_uid;_run;_cpu;_peak;_out;_err;
     _elapsed;_oom;_pids;_export_state;_omitted;_export_error;_export_digest] =
  map (fun ofs => OK (ofs,Full)) [0;4;8;12;16;20;24;32;40;48;56;64;72;80;88;96;100;104;108].
Proof. repeat split; reflexivity. Qed.

Theorem result_cells_valid : forall kind stage detail entry uid run,
  Forall (scalar_valid 144) (result_cells kind stage detail entry uid run).
Proof. intros; apply scalar_list_validb_sound; reflexivity. Qed.

Theorem result_cells_separate : forall kind stage detail entry uid run before cell rest,
  result_cells kind stage detail entry uid run = before ++ cell::rest ->
  Forall (scalar_separate cell) rest.
Proof. intros; eapply (scalar_orderedb_sound (result_cells kind stage detail entry uid run)); [reflexivity|eassumption]. Qed.

Theorem result_cells_destination_alignment : forall kind stage detail entry uid run ofs cell,
  (8 | ofs) -> In cell (result_cells kind stage detail entry uid run) ->
  (align_chunk (scalar_chunk cell) | ofs+scalar_offset cell).
Proof.
  intros kind stage detail entry uid run ofs cell [factor EQ] IN.
  unfold result_cells in IN; cbn in IN.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction; subst cell;
    cbn; rewrite EQ.
  all: cbv [Archi.align_int64].
  all: apply Z.divide_add_r.
  all: try (apply Z.mod_divide; [lia|reflexivity]).
  all: apply Z.divide_mul_r; apply Z.mod_divide; [lia|reflexivity].
Qed.

Theorem result_cells_complete : forall initial local kind stage detail entry uid run after,
  scalar_stores local initial (result_cells kind stage detail entry uid run) after ->
  result_contents after local 0 kind stage detail entry uid run.
Proof.
  intros initial local kind stage detail entry uid run after RUN cell IN; cbn.
  eapply scalar_stores_fields; [exact RUN|intros; eapply result_cells_separate; eassumption|exact IN].
Qed.

Theorem result_struct_copy_fields : forall m after local output ofs bytes kind stage detail entry uid run,
  result_contents m local 0 kind stage detail entry uid run -> (8 | ofs) ->
  Mem.loadbytes m local 0 144 = Some bytes -> Mem.storebytes m output ofs bytes = Some after ->
  result_contents after output ofs kind stage detail entry uid run.
Proof.
  intros m after local output ofs bytes kind stage detail entry uid run CONTENT ALIGN LOAD STORE cell IN.
  pose proof (Mem.loadbytes_length _ _ _ _ _ LOAD) as LENGTH.
  assert (LEN : Z.of_nat (length bytes) = 144) by (rewrite LENGTH; reflexivity).
  pose proof (result_cells_valid kind stage detail entry uid run) as VALID.
  rewrite Forall_forall in VALID. destruct (VALID cell IN) as [LOW [HIGH ALIGNED]].
  eapply copied_scalar_load with (src := local) (sofs := 0) (bytes := bytes).
  - rewrite LEN; exact LOAD.
  - exact STORE.
  - exact LOW.
  - rewrite LEN; exact HIGH.
  - eapply result_cells_destination_alignment; eassumption.
  - apply CONTENT; exact IN.
Qed.
