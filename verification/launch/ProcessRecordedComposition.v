(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Join recorded phases at their identical cursors, worlds and contexts. *)
From Stdlib Require Import List.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessSourceRecording ProcessSourceTables
  ProcessSourceWorlds ProcessCapabilityRecording.
Import ListNotations.
Local Close Scope lean_scope.

Theorem source_process_schedule_append operation groups child runs tracked other cursor worlds before
    prefix middle middle_worlds boundary suffix final final_worlds after:
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before prefix
    middle middle_worlds boundary ->
  SourceProcessSchedule operation groups child runs tracked other middle middle_worlds boundary suffix
    final final_worlds after ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before(prefix++suffix)
    final final_worlds after.
Proof. intro FIRST;induction FIRST;intro SECOND;cbn;[exact SECOND|econstructor;eauto]. Qed.

Theorem source_table_schedule_append primitive runs cursor worlds prefix middle middle_worlds suffix final final_worlds:
  SourceTableSchedule primitive runs cursor worlds prefix middle middle_worlds ->
  SourceTableSchedule primitive runs middle middle_worlds suffix final final_worlds ->
  SourceTableSchedule primitive runs cursor worlds(prefix++suffix)final final_worlds.
Proof. intro FIRST;induction FIRST;intro SECOND;cbn;[exact SECOND|econstructor;eauto]. Qed.

Theorem source_event_schedule_append primitive runs cursor prefix middle suffix final:
  SourceEventSchedule primitive runs cursor prefix middle ->
  SourceEventSchedule primitive runs middle suffix final ->
  SourceEventSchedule primitive runs cursor(prefix++suffix)final.
Proof.
  intro FIRST;induction FIRST;intro SECOND;cbn.
  - exact SECOND.
  - eapply source_event_external;eauto.
  - eapply source_event_next;eauto.
Qed.

Theorem capability_history_append operation groups runs native metadata external can_acquire owner child
    before prefix middle suffix after:
  CapabilityHistory operation groups runs native metadata external can_acquire owner child before prefix middle ->
  CapabilityHistory operation groups runs native metadata external can_acquire owner child middle suffix after ->
  CapabilityHistory operation groups runs native metadata external can_acquire owner child before(prefix++suffix)after.
Proof. intro FIRST;induction FIRST;intro SECOND;cbn;[exact SECOND|econstructor;eauto]. Qed.

Theorem recorded_run_append runs mayTrace owner child before prefix middle suffix after:
  RecordedRun runs mayTrace owner child before prefix middle ->
  RecordedRun runs mayTrace owner child middle suffix after ->
  RecordedRun runs mayTrace owner child before(prefix++suffix)after.
Proof. intro FIRST;induction FIRST;intro SECOND;cbn;[exact SECOND|econstructor;eauto]. Qed.
