(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.prefixes: Whole-routine conclusions from independent caller input. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Clight.
Require Import Slice Machine Deterministic StoreSteps Library LibraryMachine LibraryControl CallProgress Fault
  ResultLayout ResultSource ResultSafety FreshMemory DecoderLayout DecoderSource DecoderMemory
  DecoderCompare DecoderValidity DecoderInput DecoderAssembly
  SourcePaths SourceConsequences SourceGuarantees ComparisonGuarantees.
Import ListNotations.
Open Scope Z_scope.
Definition decoder_result base bytes output ofs run uid preflight sequence value after :=
  value=Vint (if decoder_accepts bytes run uid preflight sequence then Int.zero else Int.mone) /\
  (header_valid bytes run sequence=true -> decoded_contents after output ofs bytes) /\
  (header_valid bytes run sequence=false -> old_memory base after) /\
  exists local before, ~ Mem.valid_block base local /\ Mem.free before local 0 144=Some after.

Lemma decoder_prepared_result : forall base bytes output ofs run uid preflight sequence
    (memories : decoder_memories base output ofs bytes) value after,
  decoder_return_result bytes run uid preflight sequence
    (decoder_early _ _ _ _ memories) (decoder_late _ _ _ _ memories) value after ->
  decoder_result base bytes output ofs run uid preflight sequence value after.
Proof.
  intros base bytes output ofs run uid preflight sequence memories value after [VALUE MEM].
  destruct memories as [allocated local built copied early late ALLOC STORAGE EARLY LATE OLD EARLYOLD LATEP LATECONT].
  cbn in MEM. unfold decoder_result. split; [exact VALUE|].
  destruct (header_valid bytes run sequence) eqn:HEAD;cbn in MEM;subst after;
    split; [intros;exact LATECONT| |intros;discriminate|];
    split; [intros;discriminate| |intros;exact EARLYOLD|];
    exists local; [exists copied|exists allocated];split; [exact (proj1 STORAGE)|exact LATE|exact (proj1 STORAGE)|exact EARLY].
Qed.

Theorem decoder_source_connection : forall (cell : tls) base p bytes output ofs run uid preflight sequence,
  decoder_input base p bytes output ofs run uid preflight ->
  exists (memories : decoder_memories base output ofs bytes) magic count,
    store_path result_ge (result_preserved base output ofs)
      (decoder_initial p sequence output ofs Kstop base) count
      (decoder_compare_state p magic (decoder_local _ _ _ _ memories)
        (decoder_temps p sequence output ofs) (decoder_allocated _ _ _ _ memories)) /\
    memcmp_owned (decoder_allocated _ _ _ _ memories) p {|address_block:=magic;address_offset:=0|} 4 /\
    (forall comparison,
      memcmp_result (decoder_allocated _ _ _ _ memories) p {|address_block:=magic;address_offset:=0|} 4 comparison ->
      source_returns result_ge (result_preserved base output ofs)
        (decoder_result base bytes output ofs run uid preflight sequence)
        (Returnstate (Vint comparison)
          (decoder_compare_cont (decoder_local _ _ _ _ memories) (decoder_temps p sequence output ofs))
          (decoder_allocated _ _ _ _ memories))).
Proof.
  intros cell base p bytes output ofs run uid preflight sequence INPUT.
  pose proof INPUT as [LEN [READ [DEST [SEP [magic [rb [ub [pb [GLOBALS REST]]]]]]]]].
  destruct (decoder_memories_exist base output ofs bytes DEST) as [memories].
  pose proof (decoder_allocated_old _ _ _ _ memories) as OLD.
  destruct (old_decoder_globals _ _ _ _ _ _ _ _ _ OLD GLOBALS)
    as [MS [RS [US [PS [MAGIC [RUN [UID PRE]]]]]]].
  pose proof (old_memory_readable _ _ _ _ OLD READ) as RA.
  assert (PA : result_preserved base output ofs (decoder_allocated _ _ _ _ memories))
    by (apply old_decoder_preserved;exact OLD).
  assert (PM : result_preserved base output ofs base) by apply Mem.unchanged_on_refl.
  destruct (decoder_to_compare (result_preserved base output ofs) base (decoder_allocated _ _ _ _ memories)
    (decoder_local _ _ _ _ memories) p sequence output ofs magic
    (decoder_allocation _ _ _ _ memories) PM PA MS) as [count PATH].
  exists memories,magic,count;split;[exact PATH|]. split.
  - exists (firstn 4 bytes),frame_magic. split;[apply frame_prefix_owned;assumption|].
    split;[exact MAGIC|]. rewrite firstn_length,LEN;cbn;auto.
  - intros comparison RESULT. eapply source_returns_consequence.
    + exact (decoder_after_comparison_source cell base p bytes output ofs run uid preflight sequence memories comparison
        INPUT (frame_comparison_zero _ _ _ _ _ RA LEN MAGIC RESULT)).
    + auto.
    + intros; eapply decoder_prepared_result;eassumption.
Qed.

Theorem decoder_whole_source_guarantee : forall cell base p bytes output ofs run uid preflight sequence,
  decoder_input base p bytes output ofs run uid preflight ->
  procedure_guarantee result_ge cell (result_preserved base output ofs)
    (decoder_result base bytes output ofs run uid preflight sequence)
    (decoder_initial p sequence output ofs Kstop base).
Proof.
  intros cell base p bytes output ofs run uid preflight sequence INPUT.
  destruct (decoder_source_connection cell base p bytes output ofs run uid preflight sequence INPUT)
    as [memories [magic [count [PATH [OWN RETURN]]]]].
  eapply source_path_guarantee;[exact PATH|]. unfold decoder_compare_state.
  eapply memcmp_caller_guarantee;[exact OWN| |exact RETURN].
  apply old_decoder_preserved;apply decoder_allocated_old.
Qed.
Theorem decoder_all_returns : forall cell base p bytes output ofs run uid preflight sequence events value after,
  decoder_input base p bytes output ofs run uid preflight ->
  library_steps result_ge cell (live (decoder_initial p sequence output ofs Kstop base)) events
    (live (Returnstate value Kstop after)) ->
  decoder_result base bytes output ofs run uid preflight sequence value after.
Proof.
  intros. eapply procedure_return_post; [exact (proj2 (decoder_whole_source_guarantee cell base p bytes output ofs run uid preflight sequence H))|exact H0].
Qed.
Theorem decoder_all_prefixes : forall cell base p bytes output ofs run uid preflight sequence events target,
  decoder_input base p bytes output ofs run uid preflight ->
  library_steps result_ge cell (live (decoder_initial p sequence output ofs Kstop base)) events target ->
  result_preserved base output ofs (routine_memory target).
Proof. intros;exact (proj1 (decoder_whole_source_guarantee cell base p bytes output ofs run uid preflight sequence H) _ _ H0). Qed.
Theorem decoder_defined_prefix : forall cell base p bytes output ofs run uid preflight sequence events s,
  decoder_input base p bytes output ofs run uid preflight ->
  library_steps result_ge cell (live (decoder_initial p sequence output ofs Kstop base)) events (live s) ->
  (exists value after, s=Returnstate value Kstop after /\
    decoder_result base bytes output ofs run uid preflight sequence value after) \/
  (exists ev target, control_progress ev /\ library_step result_ge cell (live s) ev target).
Proof. intros;exact (proj2 (decoder_whole_source_guarantee cell base p bytes output ofs run uid preflight sequence H) _ _ H0). Qed.
Theorem decoder_freed_local_has_no_permission : forall cell base p bytes output ofs run uid preflight sequence events value after,
  decoder_input base p bytes output ofs run uid preflight ->
  library_steps result_ge cell (live (decoder_initial p sequence output ofs Kstop base)) events
    (live (Returnstate value Kstop after)) ->
  exists local, ~ Mem.valid_block base local /\
    forall pos kind permission, 0<=pos<144 -> ~ Mem.perm after local pos kind permission.
Proof.
  intros. destruct (decoder_all_returns _ _ _ _ _ _ _ _ _ _ _ _ _ H H0)
    as [_ [_ [_ [local [before [FRESH FREE]]]]]].
  exists local;split;[exact FRESH|]. intros;eapply Mem.perm_free_2;eassumption.
Qed.
