(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.input: Independent caller ownership; no acceptance or execution premises. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Clight.
Require Import Slice Library ResultLayout ResultSource ResultSafety FreshMemory
  FrameBytes DecoderLayout DecoderSource DecoderMemory DecoderValidity.
Import ListNotations.
Open Scope Z_scope.

Definition scalar_output_separate (b : block) pos chunk output ofs :=
  b <> output \/ pos+size_chunk chunk <= ofs \/ ofs+144 <= pos.
Definition decoder_globals m magic rb ub pb run uid preflight :=
  Genv.find_symbol result_ge ___stringlit_2 = Some magic /\
  Genv.find_symbol result_ge _run_id = Some rb /\ Genv.find_symbol result_ge _run_uid = Some ub /\
  Genv.find_symbol result_ge _preflight = Some pb /\
  readable_bytes m {|address_block:=magic;address_offset:=0|} frame_magic /\
  Mem.load Mint64 m rb 0 = Some (Vlong run) /\
  Mem.load Mint32 m ub 0 = Some (Vint uid) /\ Mem.load Mint32 m pb 0 = Some (Vint preflight).
Definition decoder_input m p bytes output ofs run uid preflight :=
  length bytes=160%nat /\ readable_bytes m p bytes /\ result_destination m output ofs /\
  frame_output_separate p bytes output ofs /\
  exists magic rb ub pb, decoder_globals m magic rb ub pb run uid preflight /\
    scalar_output_separate ub 0 Mint32 output ofs /\ scalar_output_separate pb 0 Mint32 output ofs.

Lemma decoder_outside_load : forall base after output ofs b pos chunk value,
  result_preserved base output ofs after -> scalar_output_separate b pos chunk output ofs ->
  Mem.load chunk base b pos = Some value -> Mem.load chunk after b pos = Some value.
Proof.
  intros base after output ofs b pos chunk value PRESERVED SEP LOAD.
  eapply Mem.load_unchanged_on; [exact PRESERVED| |exact LOAD].
  intros location RANGE; split.
  - eapply Mem.perm_valid_block. pose proof (Mem.load_valid_access _ _ _ _ _ LOAD) as [ACCESS ALIGN].
    apply ACCESS; exact RANGE.
  - destruct SEP as [NE|[BEFORE|AFTER]]; auto; [right;left|right;right]; lia.
Qed.
Lemma old_decoder_globals : forall base after magic rb ub pb run uid preflight,
  old_memory base after -> decoder_globals base magic rb ub pb run uid preflight ->
  decoder_globals after magic rb ub pb run uid preflight.
Proof.
  intros base after magic rb ub pb run uid preflight OLD [MS [RS [US [PS [MAGIC [RUN [UID PRE]]]]]]].
  split; [exact MS|]. split; [exact RS|]. split; [exact US|]. split; [exact PS|].
  split; [eapply old_memory_readable; eassumption|].
  split; [eapply old_memory_load; eassumption|]. split; eapply old_memory_load; eassumption.
Qed.
Lemma old_decoder_preserved : forall base after output ofs,
  old_memory base after -> result_preserved base output ofs after.
Proof.
  intros. eapply Mem.unchanged_on_implies; [exact H|]. intros b pos [VALID _] _; exact VALID.
Qed.
Lemma free_decoder_old : forall base before after local,
  ~ Mem.valid_block base local -> old_memory base before ->
  Mem.free before local 0 144 = Some after -> old_memory base after.
Proof.
  intros base before after local FRESH OLD FREE. eapply Mem.unchanged_on_trans; [exact OLD|].
  eapply Mem.free_unchanged_on; [exact FREE|]. intros pos RANGE VALID; contradiction.
Qed.
Lemma free_decoder_preserved : forall base before after local output ofs,
  ~ Mem.valid_block base local -> result_preserved base output ofs before ->
  Mem.free before local 0 144 = Some after -> result_preserved base output ofs after.
Proof.
  intros base before after local output ofs FRESH PRE FREE.
  eapply Mem.unchanged_on_trans; [exact PRE|].
  eapply Mem.free_unchanged_on; [exact FREE|]. intros pos RANGE [VALID _]; contradiction.
Qed.
Lemma free_decoder_contents : forall before after local output ofs bytes,
  local <> output -> decoded_contents before output ofs bytes ->
  Mem.free before local 0 144 = Some after -> decoded_contents after output ofs bytes.
Proof.
  intros before after local output ofs bytes NE CONTENT FREE cell IN.
  erewrite Mem.load_free; [apply CONTENT;exact IN|exact FREE|left;congruence].
Qed.

Record decoder_memories base output ofs bytes := {
  decoder_allocated : mem;
  decoder_local : block;
  decoder_built : mem;
  decoder_copied : mem;
  decoder_early : mem;
  decoder_late : mem;
  decoder_allocation : Mem.alloc base 0 144 = (decoder_allocated,decoder_local);
  decoder_storage_owned : decoder_storage base decoder_local decoder_allocated decoder_built decoder_copied output ofs bytes;
  decoder_free_early : Mem.free decoder_allocated decoder_local 0 144 = Some decoder_early;
  decoder_free_late : Mem.free decoder_copied decoder_local 0 144 = Some decoder_late;
  decoder_allocated_old : old_memory base decoder_allocated;
  decoder_early_old : old_memory base decoder_early;
  decoder_late_preserved : result_preserved base output ofs decoder_late;
  decoder_late_contents : decoded_contents decoder_late output ofs bytes
}.
Theorem decoder_memories_exist : forall base output ofs bytes,
  result_destination base output ofs -> inhabited (decoder_memories base output ofs bytes).
Proof.
  intros base output ofs bytes DEST.
  destruct (decoder_storage_exists base output ofs bytes DEST)
    as [allocated [local [built [copied [ALLOC STORAGE]]]]].
  pose proof STORAGE as [FRESH [LOCAL [STORES [COPY [CONTENTS [RANGE [PA PC]]]]]]].
  destruct (Mem.range_perm_free _ _ _ _ LOCAL) as [early EARLY].
  destruct (Mem.range_perm_free _ _ _ _ RANGE) as [late LATE].
  assert (OLD : old_memory base allocated) by (eapply Mem.alloc_unchanged_on;exact ALLOC).
  assert (ON : local <> output).
  { intro EQ; subst local; apply FRESH. destruct DEST as [LOW [HIGH [ALIGN WRITABLE]]].
    eapply Mem.perm_valid_block. apply WRITABLE with (ofs:=ofs);lia. }
  constructor. refine {|decoder_allocated:=allocated;decoder_local:=local;decoder_built:=built;
    decoder_copied:=copied;decoder_early:=early;decoder_late:=late;
    decoder_allocation:=ALLOC;decoder_storage_owned:=STORAGE;
    decoder_free_early:=EARLY;decoder_free_late:=LATE;decoder_allocated_old:=OLD|}.
  - eapply free_decoder_old; eassumption.
  - eapply free_decoder_preserved; eassumption.
  - eapply free_decoder_contents; eassumption.
Qed.
