(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: A genuine source CONT witnesses its actual parent's liveness. *)
From Stdlib Require Import List.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessSourceRecording ProcessSourceWorlds.
From EntryNamespace Require Import NamespaceObjects NamespaceSourceFork NamespaceGrantInputs NamespaceAdmissionGuarantee.
Import ListNotations.
Local Close Scope lean_scope.

Theorem recorded_resume_parent_alive operation groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick)
    runs cursor worlds born other final final_worlds after:
  SourceProcessSchedule operation groups child runs program other cursor worlds born ticks final final_worlds after ->
  LeanCage_Entry_CallerPhysical_Context_parentAlive
    (LeanCage_Entry_CallerPhysical_Tick_before(recorded_resume_tick recorded))=ProcessImport.Bool_true.
Proof.
  intro RUN.
  destruct(nth_error_split _ _ (recorded_resume_selected recorded))as[prefix[suffix[TICKS POSITION]]].
  rewrite TICKS in RUN.
  destruct(source_process_schedule_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)
    as[middle[middle_worlds[observed[PREFIX SUFFIX]]]].
  inversion SUFFIX as[|a b c d next next_worlds next_world rest e f g STEP TAIL];subst.
  destruct(source_process_step_selected _ _ _ _ _ _ _ _ _ _ _ _ _ _ STEP(recorded_resume_reference recorded))
    as[actual[original[snapshot'[ACTUAL[ORIGINAL[PRIMITIVE[BEFORE[AFTER VIEW]]]]]]]].
  eapply source_process_parent_live;[exact PRIMITIVE|rewrite BEFORE;exact VIEW].
Qed.

Theorem recorded_resume_parent_alive_strict operation groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick)
    runs cursor worlds born other final final_worlds after:
  SourceProcessSchedule operation groups child runs program other cursor worlds born ticks final final_worlds after ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive
    (LeanCage_Entry_CallerPhysical_Tick_before(recorded_resume_tick recorded)))ProcessImport.Bool_true.
Proof.
  intro RUN.
  rewrite(recorded_resume_parent_alive operation groups scope first snapshot run fork input owner child program channel
    ticks start read_offset read_tick recorded runs cursor worlds born other final final_worlds after RUN);constructor.
Qed.
