(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Compose actual admission and close into the physical scope checkpoint. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight Ctypes Ctypesdefs.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalTrace
  ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds ProcessSourceAdmission ProcessSourceClose.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespacePaths NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Theorem actual_source_admission_close_checkpoint operation(linux:LinuxProcessContract operation)
    groups child runs tracked other parent cursor worlds before admit_ticks middle middle_worlds admitted
    close_prefix close_tick final final_worlds after run prefix suffix guard_count
    cell admit_before admit_events admit_after close_callback close_after cgroup group status offset close_ordinal close_reply:
  SourceOtherContract other groups parent(physical_identity_task child) ->
  (forall actual,nth_error runs tracked=Some actual ->physical_identity_task(source_actor actual)=parent) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before admit_ticks
    middle middle_worlds admitted ->
  SourceProcessSchedule operation groups child runs tracked other middle middle_worlds admitted
    (close_prefix++[close_tick])final final_worlds after ->
  SourceOtherAuthority groups tracked admit_ticks ->
  SourceOtherAuthority groups tracked(close_prefix++[close_tick]) ->
  nth_error runs tracked=Some run ->
  source_events run=prefix++map namespace_process admit_events++
    (repeat namespace_source_event guard_count++close_callback)++suffix ->
  cursor tracked=length prefix ->middle tracked=(length prefix+length admit_events)%nat ->
  final tracked=(length prefix+length admit_events+guard_count+length close_callback)%nat ->
  status<>tls_block cell ->Mem.valid_block admit_before(tls_block cell) ->
  OwnsUnreaped before parent(physical_identity_task child) ->process_cgroup_files before parent cgroup=Some group ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)
      [Vint(task_pid(physical_identity_task child));Vint cgroup;Vptr status offset]Kstop admit_before))admit_events
    (live(Returnstate(Vint Int.zero)Kstop admit_after)) ->
  namespace_steps admission_ge cell(live(Callstate close_definition[Vint cgroup]Kstop admit_after))close_callback
    (live(Returnstate(Vint Int.zero)Kstop close_after)) ->
  LeanCage_Entry_CallerPhysical_Tick_source close_tick=source_reference tracked close_ordinal ->
  nth_error(source_events run)close_ordinal=
    Some(namespace_process(process_entry(entry_library(close_returned cgroup close_reply)))) ->
  Lean.eq
    (LeanCage_Entry_CallerPhysical_Context_cgroup(LeanCage_Entry_CallerPhysical_Tick_after close_tick))
    (ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group)).
Proof.
  intros CONTRACT ACTOR ADMISSION CLOSE ADMIT_AUTH CLOSE_AUTH PROGRAM EVENTS START ADMITTED FINISH
    SEPARATE TLS OWNER FILE ADMIT_SOURCE CLOSE_SOURCE REFERENCE CLOSE_EVENT.
  assert(POSITIVE:1<=Int.signed(task_pid(physical_identity_task child))).
  { rewrite physical_identity_task_pid;exact(proj1(physical_identity_pid_range child)). }
  assert(ADMIT_EVENTS:source_events run=prefix++map namespace_process admit_events++
    ((repeat namespace_source_event guard_count++close_callback)++suffix)).
  { rewrite EVENTS;repeat rewrite app_assoc;reflexivity. }
  destruct(source_process_admission_from_source_slice operation linux groups child runs tracked other parent
    cursor worlds before admit_ticks middle middle_worlds admitted run prefix
    ((repeat namespace_source_event guard_count++close_callback)++suffix)
    cell admit_before admit_events admit_after cgroup group status offset
    CONTRACT ACTOR ADMISSION ADMIT_AUTH PROGRAM ADMIT_EVENTS START ADMITTED POSITIVE SEPARATE TLS OWNER FILE ADMIT_SOURCE)
    as[ADMIT_OWNER ADMIT_GROUP].
  destruct(source_namespace_guard_close_quiet admission_ge cell admit_after cgroup guard_count close_callback
    (Vint Int.zero)close_after CLOSE_SOURCE)
    as[close_events[GUARD_EVENTS CLOSE_QUIET]].
  assert(CLOSE_EVENTS:source_events run=(prefix++map namespace_process admit_events)++
    map namespace_process close_events++suffix).
  { rewrite EVENTS,<-GUARD_EVENTS;repeat rewrite app_assoc;reflexivity. }
  assert(CLOSE_START:middle tracked=length(prefix++map namespace_process admit_events)).
  { rewrite length_app,length_map;exact ADMITTED. }
  assert(CLOSE_FINISH:final tracked=(length(prefix++map namespace_process admit_events)+length close_events)%nat).
  { pose proof(f_equal(@length namespace_event)GUARD_EVENTS)as LENGTH.
    rewrite length_app,repeat_length,length_map in LENGTH.
    rewrite length_app,length_map;lia. }
  assert(QUIET:Forall(fun event=>process_quiet_event event=true)
    (source_program_process_events runs tracked(close_prefix++[close_tick]))).
  { rewrite(source_process_schedule_event_slice operation groups child runs tracked other middle middle_worlds admitted
      (close_prefix++[close_tick])final final_worlds after run(prefix++map namespace_process admit_events)
      close_events suffix CLOSE PROGRAM CLOSE_EVENTS CLOSE_START CLOSE_FINISH).
    exact CLOSE_QUIET. }
  eapply source_process_scope_to_close_checkpoint;try eassumption.
Qed.
