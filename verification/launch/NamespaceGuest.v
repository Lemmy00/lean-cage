(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Every actual child run projects to the proved guest machine. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine LibraryMachine LibraryControl CallProgressDraft.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffMemory NativeHandoffEncoding NativeHandoffGuest
  NativeHandoffExec NativeHandoffImage HandoffRegion.
From EntryFailure Require Import FailureSource FailureProgress FailureMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceEntry.
Import ListNotations.

Lemma namespace_progressing_library_is_entry_defined ge cell start :
  live_progress ge cell start ->namespace_entry_defined ge cell start.
Proof.
  intros PROGRESS events current RUN.
  destruct(progressing_entry_run_is_library _ _ _ _ _ PROGRESS RUN)as[original[EVENTS REAL]].
  destruct(PROGRESS _ _ REAL)as[event[target[ADVANCE STEP]]].
  exists(entry_library event),target;split;[exact ADVANCE|apply entry_library_step;exact STEP].
Qed.

Theorem namespace_failure_is_entry_defined cell memory failure stage error k :
  entry_errno_ready cell memory ->is_call_cont k ->
  namespace_entry_defined handoff_ge cell
    (Callstate(Internal f_fail_child)[Vint failure;Vint stage;Vint error]k memory).
Proof.
  intros ERRNO CALL.
  change(namespace_entry_defined failure_ge cell(failure_initial failure stage error k memory)).
  apply namespace_progressing_library_is_entry_defined.
  apply current_failure_all_prefixes;[apply entry_errno_ready_tls;exact ERRNO|exact CALL].
Qed.

Theorem namespace_exec_is_entry_defined cell b caller memory failure k :
  caller!_failure=Some(Vint failure) ->
  namespace_entry_defined handoff_ge cell
    (Callstate entry_exec_definition
      [Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(NativeHandoffStructure.guest_tail 24(fn_body f_guest))k))memory).
Proof.
  intro FAILURE;intros events;revert memory.
  induction events as[|event rest IH];intros memory current RUN.
  - inversion RUN;subst.
    eexists(entry_image(Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero)
      (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)).
    exists(dead memory);split;[exact I|apply entry_exec_image_step].
  - inversion RUN;subst.
    match goal with STEP:entry_handoff_step _ _ _ _ _|-_=>
      destruct(handoff_exec_cases _ _ _ _ _ _ _ _ _ STEP)
        as[[returned[after[FRAME[READY[EVENT TARGET]]]]]|[[EVENT TARGET]|
          [[after[PARTIAL[EVENT TARGET]]]|[[EVENT TARGET]|[EVENT TARGET]]]]]end;subst.
    + eapply namespace_region_defined.
      * exact(handoff_exec_return_failure_region cell b caller after returned failure k FAILURE READY).
      * intros endpoint[error[final[SAME RANGE]]];subst endpoint.
        apply namespace_failure_is_entry_defined;[exact READY|exact I].
      * eassumption.
    + eapply IH;eassumption.
    + match goal with TAIL:entry_handoff_steps _ _ (dead _) _ (live _)|-_=>
        destruct(entry_handoff_dead_steps _ _ _ _ _ TAIL)as[NONE IMPOSSIBLE];discriminate end.
    + match goal with TAIL:entry_handoff_steps _ _ (dead _) _ (live _)|-_=>
        destruct(entry_handoff_dead_steps _ _ _ _ _ TAIL)as[NONE IMPOSSIBLE];discriminate end.
    + match goal with TAIL:entry_handoff_steps _ _ (dead _) _ (live _)|-_=>
        destruct(entry_handoff_dead_steps _ _ _ _ _ TAIL)as[NONE IMPOSSIBLE];discriminate end.
Qed.

Theorem namespace_guest_is_entry_defined cell input before input_fd output_fd errors_fd failure k :
  handoff_borrowed_input cell before input ->namespace_entry_defined handoff_ge cell
    (Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before).
Proof.
  intro INPUT;eapply namespace_region_defined.
  - apply handoff_guest_region;exact INPUT.
  - intros endpoint[FAILED|IMAGE].
    + destruct FAILED as[stage[error[call[memory[SAME[STAGE[RANGE[READY CALL]]]]]]]];subst endpoint.
      apply namespace_failure_is_entry_defined;assumption.
    + destruct IMAGE as[b[after[caller[uidbytes[fdtexts[suffix[SAME[FAILURE REST]]]]]]]];subst endpoint.
      eapply namespace_exec_is_entry_defined with(failure:=failure);exact FAILURE.
Qed.

Theorem actual_namespace_guest_projects cell input before input_fd output_fd errors_fd failure k events target :
  handoff_borrowed_input cell before input ->
  namespace_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))events target ->
  exists actual,events=map(fun event=>namespace_process(ProcessMachine.process_entry event))actual /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))actual target.
Proof.
  intros INPUT RUN;eapply namespace_defined_run_projects;
    [eapply namespace_guest_is_entry_defined with(input:=input);exact INPUT|exact RUN].
Qed.
