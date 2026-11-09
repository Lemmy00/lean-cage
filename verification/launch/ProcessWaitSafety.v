(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Every finite helper prefix requires the owned child's SIGSTOP before setup. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps ErrorNumber LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessReturns
  ProcessPaths ProcessWait ProcessStatus ProcessWaitRejection ProcessPrimitiveCases ProcessRoutine.
Import ListNotations.
Open Scope Z_scope.

Definition admission_later_event event :=
  match event with
  | process_waited _ _ _ _ _ |process_wait_lost _ _ _ _ |process_waiting=>false
  | process_entry(entry_library(original_event(source_step _)))=>false
  | process_entry(entry_library(original_event errno_step))=>false
  | process_entry(entry_library(original_event loss_step))=>false
  | _=>true
  end.

Definition admission_stopped_event child status offset event :=exists word,
  event=process_waited child status offset Int.zero(wait_status child word) /\
  admission_is_stopped word=true /\admission_is_sigstop word=true.

Inductive admission_unstopped cell(child:int)(status:block)(offset:Ptrofs.int):machine->Prop:=
| admission_pending_wait:forall state count locals le memory,
    le!_child=Some(Vint child) ->le!_status=Some(Vptr status offset) ->
    store_path admission_ge(fun _=>True)state count
      (Callstate process_wait_definition[Vint child;Vptr status offset;Vint Int.zero]
        (admission_wait_call_cont(admission_env locals)le Kstop)memory) ->
    admission_unstopped cell child status offset(live state)
| admission_pending_errno:forall state count locals le memory error,
    le!_child=Some(Vint child) ->le!_status=Some(Vptr status offset) ->
    initialized_errno cell memory error ->
    store_path admission_ge(fun _=>True)state count
      (Callstate(External errno_function[](tptr tint)cc_default)[]
        (admission_errno_cont(admission_env locals)le Kstop)memory) ->
    admission_unstopped cell child status offset(live state)
| admission_pending_rejection:forall state count locals le memory k,
    call_cont k=Kstop ->store_path admission_ge(fun _=>True)state count
      (State f_admit_child admission_failure k(admission_env locals)le memory) ->
    admission_unstopped cell child status offset(live state)
| admission_stopped_return:forall value memory,
    admission_unstopped cell child status offset(live(Returnstate value Kstop memory))
| admission_stopped_dead:forall memory,admission_unstopped cell child status offset(dead memory).

Theorem admission_unstopped_step cell child status offset state event target :
  1<=Int.signed child ->status<>tls_block cell ->
  admission_unstopped cell child status offset state ->
  process_step admission_ge cell state event target ->
  admission_later_event event=false /\
    (admission_stopped_event child status offset event \/
      admission_unstopped cell child status offset target).
Proof.
  intros POSITIVE SEPARATE INVARIANT STEP;destruct INVARIANT as
    [state count locals le memory CHILD STATUS PATH|
     state count locals le memory error CHILD STATUS ERRNO PATH|
     state count locals le memory k CLOSED PATH|value memory|memory].
  - inversion PATH as[current GOOD|current next rest last GOOD EDGE TAIL];subst.
    + destruct(process_wait_cases _ _ _ _ _ _ _ _ _ _ STEP)
        as[[observation[after[EFFECT[ERRNO[EVENT TARGET]]]]]|[[EVENT TARGET]|
          [[EVENT TARGET]|[after[EVENT[PARTIAL TARGET]]]]]];subst.
      * split;[reflexivity|]. destruct observation as[error|got word].
        -- right;eapply admission_pending_errno;[exact CHILD|exact STATUS| |].
           ++ eapply admission_failed_errno_readback;eassumption.
           ++ apply admission_wait_failed_to_errno;apply admission_nonlocal_binding;discriminate.
        -- destruct(admission_wait_status_readback _ _ _ _ _ _ _ SEPARATE EFFECT)as[GOT LOAD].
           destruct(admission_stop_matches child got word)eqn:MATCHES.
           ++ left;unfold admission_stop_matches in MATCHES.
              apply andb_true_iff in MATCHES as[MATCHES SIGNAL].
              apply andb_true_iff in MATCHES as[SAME STOPPED].
              apply Int.same_if_eq in SAME;subst got;exists word;auto.
           ++ right;destruct(admission_rejected_status_source locals le after Kstop got child status offset word
                ltac:(lia)CHILD STATUS LOAD MATCHES)as[count[final[k[CLOSED REJECT]]]].
              eapply admission_pending_rejection;[exact CLOSED|exact REJECT].
      * split;[reflexivity|right]. eapply admission_pending_wait;
          [exact CHILD|exact STATUS|constructor;exact I].
      * split;[reflexivity|right;constructor].
      * split;[reflexivity|right;constructor].
    + destruct(process_store_edge_cases _ _ _ _ _ _ EDGE STEP)as[[EVENT TARGET]|[EVENT TARGET]];
        subst;split;[reflexivity| |reflexivity|right;constructor].
      right;eapply admission_pending_wait;eassumption.
  - inversion PATH as[current GOOD|current next rest last GOOD EDGE TAIL];subst.
    + destruct(process_certain_step_cases _ _ _ _ _ _ _
        (ErrorNumber.errno_certain admission_ge cell(admission_errno_cont(admission_env locals)le Kstop)
          memory error ERRNO)STEP)as[[EVENT TARGET]|[EVENT TARGET]];subst.
      * split;[reflexivity|right].
        destruct(admission_errno_rejoins cell locals le memory child status offset error
          POSITIVE CHILD STATUS ERRNO)as[[count RETRY]|[count[final[k[CLOSED REJECT]]]]].
        -- eapply admission_pending_wait;[| |exact RETRY];
             unfold admission_errno_env,admission_wait_saved;
             repeat rewrite PTree.gso by discriminate;assumption.
        -- eapply admission_pending_rejection;[exact CLOSED|exact REJECT].
      * split;[reflexivity|right;constructor].
    + destruct(process_store_edge_cases _ _ _ _ _ _ EDGE STEP)as[[EVENT TARGET]|[EVENT TARGET]];
        subst;split;[reflexivity| |reflexivity|right;constructor].
      right;eapply admission_pending_errno;eassumption.
  - inversion PATH as[current GOOD|current next rest last GOOD EDGE TAIL];subst.
    + unfold admission_failure in STEP.
      destruct(process_return_statement_terminates _ _ _ _ _ _ _ _ _ _ CLOSED STEP)
        as[[EVENT[value[after TARGET]]]|[EVENT TARGET]];subst;
        split;[reflexivity|right;constructor|reflexivity|right;constructor].
    + destruct(process_store_edge_cases _ _ _ _ _ _ EDGE STEP)as[[EVENT TARGET]|[EVENT TARGET]];
        subst;split;[reflexivity| |reflexivity|right;constructor].
      right;eapply admission_pending_rejection;eassumption.
  - destruct(process_stopped_return_only_loss _ _ _ _ _ _ STEP)as[EVENT TARGET];subst.
    split;[reflexivity|right;constructor].
  - exfalso;eapply process_dead_cannot_resume;exact STEP.
Qed.

Theorem admission_initial_unstopped cell before child cgroup status offset :
  admission_unstopped cell child status offset
    (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status offset]Kstop before)).
Proof.
  destruct(admission_allocate before)as[locals[after[ALLOC OBJECTS]]].
  eapply admission_pending_wait with(locals:=locals)
    (le:=admission_parameters child cgroup(Vptr status offset))(memory:=after)(count:=5%nat).
  - unfold admission_parameters;WriteAll.lookup.
  - unfold admission_parameters;WriteAll.lookup.
  - apply admission_start_to_wait;exact ALLOC.
Qed.

Theorem admission_prefix_classification cell child status offset start events target :
  1<=Int.signed child ->status<>tls_block cell ->
  admission_unstopped cell child status offset start ->
  process_steps admission_ge cell start events target ->
  (exists event,In event events /\admission_stopped_event child status offset event) \/
    admission_unstopped cell child status offset target.
Proof.
  intros POSITIVE SEPARATE INVARIANT RUN;revert INVARIANT;
    induction RUN;intros INVARIANT;[right;exact INVARIANT|].
  destruct(admission_unstopped_step _ _ _ _ _ _ _ POSITIVE SEPARATE INVARIANT H)
    as[_[STOPPED|NEXT]].
  - left;exists event;split;[left;reflexivity|exact STOPPED].
  - destruct(IHRUN NEXT)as[[observed[MEMBER STOPPED]]|FINAL].
    + left;exists observed;split;[right;exact MEMBER|exact STOPPED].
    + right;exact FINAL.
Qed.

Theorem admission_setup_requires_matching_stop cell before child cgroup status offset events target :
  1<=Int.signed child ->status<>tls_block cell ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status offset]Kstop before))events target ->
  forall prefix event suffix,events=prefix++event::suffix ->admission_later_event event=true ->
    exists observed,In observed prefix /\admission_stopped_event child status offset observed.
Proof.
  intros POSITIVE SEPARATE RUN prefix event suffix EVENTS LATER;subst events.
  destruct(process_steps_split _ _ _ _ _ _ RUN)as[middle[PREFIX REST]].
  destruct(admission_prefix_classification _ _ _ _ _ _ _ POSITIVE SEPARATE
    (admission_initial_unstopped _ _ _ _ _ _)PREFIX)as[STOPPED|INVARIANT];[exact STOPPED|].
  inversion REST;subst.
  match goal with STEP:process_step _ _ _ _ _|-_=>
    destruct(admission_unstopped_step _ _ _ _ _ _ _ POSITIVE SEPARATE INVARIANT STEP)as[NONE _]end.
  congruence.
Qed.
