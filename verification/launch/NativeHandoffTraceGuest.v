(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The maintained guest emits its checked descriptor operations on the image run. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffInitial NativeHandoffMemory NativeHandoffDescriptors NativeHandoffLoop
  NativeHandoffExec NativeHandoffTables NativeHandoffGuest NativeHandoffTracePaths NativeHandoffTraceChecks
  NativeHandoffTraceInitial NativeHandoffTraceEncoding NativeHandoffTraceLoop.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.
Ltac handoff_trace_route := eapply handoff_trace_spec_edge;[apply unchanged_store_edge;WriteAll.structural|].

Definition handoff_trace_exec_ready failure state := exists b after caller suffix,
  state=Callstate entry_exec_definition
    [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
     Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
    (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))suffix))after /\
  caller!EntrySource._failure=Some(Vint failure).

Lemma handoff_expected_flags_actual input_fd output_fd errors_fd failure :
  handoff_trace_descriptor_events(handoff_original_words input_fd output_fd errors_fd failure)0 4++
    [handoff_flag_event Int.one Int.one Int.zero]=handoff_expected_flags input_fd output_fd errors_fd failure.
Proof. reflexivity. Qed.

Theorem handoff_trace_guest_normal cell input before input_fd output_fd errors_fd failure k :
  handoff_trace_failure_safe cell ->handoff_borrowed_input cell before input ->
  handoff_borrowed_mode_bytes input=handoff_normal_bytes ->
  100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 ->
  handoff_descriptors_checked(handoff_original_words input_fd output_fd errors_fd failure)4 ->
  handoff_trace_spec handoff_ge cell(handoff_trace_exec_ready failure)
    (handoff_expected_flags input_fd output_fd errors_fd failure)
    (Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before).
Proof.
  intros SAFE INPUT MODE UIDBOUND CHECKED.
  eapply handoff_trace_initial;[exact INPUT|exact MODE|exact UIDBOUND|].
  intros b initialized initialle LAYOUT LIVE FAILURE.
  refine(handoff_trace_uid cell input b(handoff_original_words input_fd output_fd errors_fd failure)
    initialized initialle k failure(handoff_trace_exec_ready failure)
    (handoff_expected_flags input_fd output_fd errors_fd failure)SAFE LAYOUT LIVE UIDBOUND FAILURE _).
  intros uid_after uidle UIDLIVE UIDFAILURE.
  rewrite handoff_descriptors_tail_actual at 1;handoff_trace_route.
  rewrite <- handoff_expected_flags_actual.
  refine(handoff_trace_descriptors cell input b(handoff_original_words input_fd output_fd errors_fd failure)
    uid_after uidle(Kseq(guest_tail 10(fn_body EntrySource.f_guest))k)failure(handoff_trace_exec_ready failure)
    [handoff_flag_event Int.one Int.one Int.zero]SAFE LAYOUT UIDLIVE UIDFAILURE CHECKED _).
  intros fd_after fdle FDLIVE FDFAILURE;handoff_trace_route.
  change(handoff_trace_spec handoff_ge cell(handoff_trace_exec_ready failure)
    (handoff_flag_event Int.one Int.one Int.zero::[])
    (State EntrySource.f_guest(guest_tail 10(fn_body EntrySource.f_guest))k(handoff_locals_env b)fdle fd_after)).
  refine(handoff_trace_stdout cell input b(handoff_original_words input_fd output_fd errors_fd failure)
    fd_after fdle k failure(handoff_trace_exec_ready failure)[]SAFE LAYOUT FDLIVE FDFAILURE _).
  intros stdout_after stdoutle STDOUTLIVE STDOUTFAILURE.
  destruct(handoff_argument_tables_source cell input b(handoff_original_words input_fd output_fd errors_fd failure)
    stdout_after stdoutle k failure LAYOUT STDOUTLIVE STDOUTFAILURE)
    as[after[count[copied[COUNTBOUND[AFTER[TABLEFRAME[ARGSTABLE[ENVTABLE[FINALFAILURE PATH]]]]]]]]].
  eapply handoff_trace_spec_source;[exact PATH|]. apply handoff_trace_spec_here.
  exists b,after,(handoff_checked_argument_env copied(handoff_borrowed_source input)(handoff_borrowed_source_offset input)),k.
  split;[reflexivity|]. unfold handoff_checked_argument_env;rewrite !PTree.gso by discriminate;exact FINALFAILURE.
Qed.
