(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Retain the parent's actual file view through the same source prefix. *)
From Stdlib Require Import ZArith Arith List Lia.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessJournal ProcessOwnership ProcessPhysicalTrace
  ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds.
From EntryNamespace Require Import NamespaceMachine NamespaceKernel NamespacePhysical.
Import ListNotations.

Lemma source_table_other_world primitive runs cursor worlds tick middle middle_worlds tracked:
  SourceTableStep primitive runs cursor worlds tick middle middle_worlds ->
  (forall ordinal,ProcessImport.LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference tracked ordinal) ->
  middle_worlds tracked=worlds tracked.
Proof.
  intros STEP OUTSIDE;destruct STEP.
  - reflexivity.
  - assert(OTHER:tracked<>program).
    { intro SAME;subst program;exact(OUTSIDE(cursor tracked)H1). }
    unfold source_world_next;assert(NE:Nat.eqb tracked program=false)by(apply Nat.eqb_neq;exact OTHER).
    rewrite NE;reflexivity.
Qed.

Lemma source_file_view_frame groups before after parent namespace changed:
  SourceFileView groups before parent namespace ->
  process_cgroup_files after parent=process_cgroup_files before parent ->changed=namespace ->
  SourceFileView groups after parent changed.
Proof. intros VIEW FILES SAME;subst changed;unfold SourceFileView in *;rewrite FILES;exact VIEW. Qed.

Theorem source_process_schedule_files operation(linux:LinuxProcessContract operation)
    groups child runs tracked other parent cursor worlds before ticks final final_worlds after:
  SourceOtherContract other groups parent(physical_identity_task child) ->
  (forall run,nth_error runs tracked=Some run ->physical_identity_task(source_actor run)=parent) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  OwnsUnreaped before parent(physical_identity_task child) ->SourceOtherAuthority groups tracked ticks ->
  Forall(fun event=>process_nonreaping event=true)(source_program_process_events runs tracked ticks) ->
  SourceFileView groups before parent(worlds tracked) ->
  OwnsUnreaped after parent(physical_identity_task child) /\SourceFileView groups after parent(final_worlds tracked).
Proof.
  intros CONTRACT ACTOR RUN;induction RUN;intros OWNER AUTHORITY EVENTS FILES.
  - split;assumption.
  - assert(TAIL_AUTHORITY:SourceOtherAuthority groups tracked ticks).
    { constructor;intros selected MEMBER OUTSIDE.
      - eapply source_other_quiet;[exact AUTHORITY|right;exact MEMBER|exact OUTSIDE].
      - eapply source_other_live;[exact AUTHORITY|right;exact MEMBER|exact OUTSIDE]. }
    destruct H as[cursor worlds tick run original snapshot PROGRAM EVENT SOURCE PRIMITIVE BEFORE PARENT_BEFORE PARENT_AFTER|
      cursor worlds before tick middle middle_worlds observed STEP OUTSIDE OTHER].
    + unfold source_program_process_events,source_program_events in EVENTS;cbn in EVENTS.
      unfold source_program_event in EVENTS;rewrite SOURCE in EVENTS.
      cbn[ProcessJournal.source_reference]in EVENTS;rewrite !Lean.nat2Natid,Nat.eqb_refl,PROGRAM,EVENT in EVENTS.
      cbn in EVENTS;inversion EVENTS as[|head tail NONREAP REMAINING];subst head tail.
      pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE original(Logic.eq_refl _))as KERNEL.
      rewrite(ACTOR _ PROGRAM)in KERNEL.
      assert(NEXT_OWNER:OwnsUnreaped(source_process_after snapshot)parent(physical_identity_task child)).
      { eapply(linux_nonreaping_owner _ linux);[exact OWNER|exact NONREAP|exact KERNEL]. }
      apply IHRUN;[exact NEXT_OWNER|exact TAIL_AUTHORITY|exact REMAINING|].
      unfold source_world_next;rewrite Nat.eqb_refl.
      rewrite <-(ACTOR _ PROGRAM);eapply source_primitive_files_after;exact PRIMITIVE.
    + pose proof(source_program_event_outside runs tracked tick OUTSIDE)as EMPTY.
      unfold source_program_process_events,source_program_events in EVENTS;cbn in EVENTS.
      rewrite EMPTY in EVENTS;cbn in EVENTS.
      pose proof(source_other_quiet _ _ _ AUTHORITY tick ltac:(left;reflexivity)OUTSIDE)as QUIET.
      pose proof(source_other_live _ _ _ AUTHORITY tick ltac:(left;reflexivity)OUTSIDE)as LIVE.
      pose proof(source_other_interference _ _ _ _ CONTRACT _ _ _ OWNER OTHER QUIET LIVE)as INTERFERENCE.
      assert(NEXT_OWNER:OwnsUnreaped observed parent(physical_identity_task child)).
      { eapply unreaped_owner_survives_interference;[exact OWNER|exact INTERFERENCE]. }
      apply IHRUN;[exact NEXT_OWNER|exact TAIL_AUTHORITY|exact EVENTS|].
      eapply source_file_view_frame;[exact FILES|exact(interference_files _ _ _ _ INTERFERENCE)|].
      eapply source_table_other_world;[exact STEP|exact OUTSIDE].
Qed.
