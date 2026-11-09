(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Every finite actual helper prefix emits bytes only after checked resume. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine StoreSteps ClightSteps LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessPaths ProcessRelease
  ProcessPrimitiveCases.
Import ListNotations.
Open Scope Z_scope.

Definition process_transports event :=
  match event with
  | process_entry (entry_library (original_event (io_step _ _))) => true
  | process_entry (entry_library (original_event (partial_loss _ _ _))) => true
  | _ => false
  end.
Definition release_resume_event child :=
  process_traced (Int.repr 7) child (Vlong Int64.zero) (Vlong Int64.zero) Int64.zero.

Inductive release_unresumed (child : int) : machine -> Prop :=
| release_pending_resume : forall state count grant le memory,
    store_path admission_ge (fun _ => True) state count
      (Callstate process_ptrace_definition
        [Vint (Int.repr 7);Vint child;Vlong Int64.zero;Vlong Int64.zero]
        (release_resume_cont grant le Kstop) memory) ->
    release_unresumed child (live state)
| release_pending_failure : forall state count grant le memory k,
    call_cont k = Kstop ->
    store_path admission_ge (fun _ => True) state count
      (State f_release_child release_failure k (release_env grant) le memory) ->
    release_unresumed child (live state)
| release_closed_return : forall value memory,
    release_unresumed child (live (Returnstate value Kstop memory))
| release_closed_dead : forall memory, release_unresumed child (dead memory).

Theorem release_unresumed_step cell child state event target :
  release_unresumed child state -> process_step admission_ge cell state event target ->
  process_transports event = false /\
    (event = release_resume_event child \/ release_unresumed child target).
Proof.
  intros INVARIANT STEP; destruct INVARIANT as
    [state count grant le memory PATH|state count grant le memory k CLOSED PATH|value memory|memory].
  - inversion PATH as [current GOOD|current next rest last GOOD EDGE TAIL]; subst.
    + destruct (process_ptrace_cases _ _ _ _ _ _ _ _ _ _ STEP)
        as [[returned [after [FRAME [ERRNO [EVENT TARGET]]]]]|[[EVENT TARGET]|
          [[EVENT TARGET]|[after [EVENT [PARTIAL TARGET]]]]]];subst.
      * split;[reflexivity|]. destruct (release_resumed returned) eqn:RESUMED.
        -- left; unfold release_resumed in RESUMED.
           apply Int64.same_if_eq in RESUMED;subst;reflexivity.
        -- right; eapply release_pending_failure with
             (count:=3%nat) (k:=Kseq (release_tail 2) Kstop);[reflexivity|].
           pose proof (release_resume_return_source grant le after Kstop returned) as CONTINUE.
           rewrite RESUMED in CONTINUE;exact CONTINUE.
      * split;[reflexivity|right]. eapply release_pending_resume;constructor;exact I.
      * split;[reflexivity|right;constructor].
      * split;[reflexivity|right;constructor].
    + destruct (process_store_edge_cases _ _ _ _ _ _ EDGE STEP)
        as [[EVENT TARGET]|[EVENT TARGET]];subst;split;[reflexivity| |reflexivity|].
      * right;eapply release_pending_resume;exact TAIL.
      * right;constructor.
  - inversion PATH as [current GOOD|current next rest last GOOD EDGE TAIL];subst.
    + unfold release_failure in STEP.
      destruct (process_return_statement_terminates _ _ _ _ _ _ _ _ _ _ CLOSED STEP)
        as [[EVENT [value [after TARGET]]]|[EVENT TARGET]];subst;
        split;[reflexivity|right;constructor|reflexivity|right;constructor].
    + destruct (process_store_edge_cases _ _ _ _ _ _ EDGE STEP)
        as [[EVENT TARGET]|[EVENT TARGET]];subst;split;[reflexivity| |reflexivity|].
      * right;eapply release_pending_failure;[exact CLOSED|exact TAIL].
      * right;constructor.
  - destruct (process_stopped_return_only_loss _ _ _ _ _ _ STEP) as [EVENT TARGET];subst.
    split;[reflexivity|right;constructor].
  - exfalso;eapply process_dead_cannot_resume;exact STEP.
Qed.

Theorem release_unresumed_prefix cell child start events target :
  release_unresumed child start -> process_steps admission_ge cell start events target ->
  ~In (release_resume_event child) events -> release_unresumed child target.
Proof.
  intros INVARIANT RUN;revert INVARIANT;induction RUN;intros INVARIANT ABSENT;[exact INVARIANT|].
  destruct (release_unresumed_step _ _ _ _ _ INVARIANT H) as [_ [RESUMED|NEXT]].
  - exfalso;apply ABSENT;left;exact RESUMED.
  - apply IHRUN;[exact NEXT|]. intro MEMBER;apply ABSENT;right;exact MEMBER.
Qed.

Theorem release_prefix_classification cell child start events target :
  release_unresumed child start -> process_steps admission_ge cell start events target ->
  In (release_resume_event child) events \/ release_unresumed child target.
Proof.
  intros INVARIANT RUN;revert INVARIANT;induction RUN;intros INVARIANT;[right;exact INVARIANT|].
  destruct (release_unresumed_step _ _ _ _ _ INVARIANT H) as [_ [RESUMED|NEXT]].
  - left;left;exact RESUMED.
  - destruct (IHRUN NEXT) as [PRESENT|FINAL];[left;right;exact PRESENT|right;exact FINAL].
Qed.

Theorem release_initial_unresumed before child peer :
  release_unresumed child
    (live (Callstate (Internal f_release_child) [Vint child;Vint peer] Kstop before)).
Proof.
  destruct (Mem.alloc before 0 1) as [allocated grant] eqn:ALLOC.
  assert (ACCESS : Mem.valid_access allocated Mint8unsigned grant 0 Freeable).
  { eapply Mem.valid_access_alloc_same;[exact ALLOC|lia|cbn;lia|exists 0;reflexivity]. }
  assert (WRITE : Mem.valid_access allocated Mint8unsigned grant 0 Writable).
  { eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr 165)) WRITE) as [after STORE].
  eapply release_pending_resume; eapply release_start_to_resume; eassumption.
Qed.

Theorem release_transport_requires_checked_resume cell before child peer events target :
  process_steps admission_ge cell
    (live (Callstate (Internal f_release_child) [Vint child;Vint peer] Kstop before)) events target ->
  forall prefix event suffix, events = prefix++event::suffix -> process_transports event = true ->
    In (release_resume_event child) prefix.
Proof.
  intros RUN prefix event suffix EVENTS TRANSPORT;subst events.
  destruct (process_steps_split _ _ _ _ _ _ RUN) as [middle [PREFIX REST]].
  destruct (release_prefix_classification _ _ _ _ _ (release_initial_unresumed _ _ _) PREFIX)
    as [PRESENT|INVARIANT];[exact PRESENT|].
  inversion REST;subst.
  match goal with STEP : process_step _ _ _ _ _ |- _ =>
    destruct (release_unresumed_step _ _ _ _ _ INVARIANT STEP) as [NONE _] end.
  congruence.
Qed.
