(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Carry one fork-owned incarnation through the same actual admission trace. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessStatus ProcessOwnership.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceWorldTrace.
Import ListNotations.
Open Scope Z_scope.

(* A single Linux fork supplies the PID slot and parent edge. Its default
   SIGCHLD effect uses the action observed by the source-indexed namespace
   trace. Exclusive native waiting is an explicit runtime/bootstrap premise. *)
Record ForkProcessEffect (namespace:NamespaceWorld) (before:ProcessWorld)
    (snapshot:ForkSnapshot) (after:ProcessWorld) : Prop := {
  fork_process_matches : fork_matches namespace snapshot;
  fork_process_fresh : process_pid before(task_pid(fork_child snapshot))=None;
  fork_process_slot : process_pid after(task_pid(fork_child snapshot))=Some(fork_child snapshot);
  fork_process_parent : owned_parent(process_tasks after(fork_child snapshot))=fork_parent snapshot;
  fork_process_default_reap : namespace_sigchld namespace=default_signal_action ->
    process_explicit_reap after(fork_parent snapshot)=true;
  fork_process_sole_waiter : process_sole_waiter after(fork_parent snapshot)=
    process_sole_waiter before(fork_parent snapshot);
  fork_process_cgroup_files : process_cgroup_files after(fork_parent snapshot)=
    process_cgroup_files before(fork_parent snapshot)
}.

Theorem source_default_fork_produces_unreaped namespace before snapshot after :
  ForkProcessEffect namespace before snapshot after ->
  namespace_sigchld namespace=default_signal_action ->
  process_sole_waiter before(fork_parent snapshot)=true ->
  OwnsUnreaped after(fork_parent snapshot)(fork_child snapshot).
Proof.
  intros EFFECT DEFAULT SOLE;destruct EFFECT.
  split;[exact fork_process_slot0|]. split;[exact fork_process_parent0|].
  split;[apply fork_process_default_reap0;exact DEFAULT|congruence].
Qed.

(* Interference remains permitted between every two source events. A kernel
   operation's post-state is its linearization snapshot; it is not a promise
   that the child will remain alive when a later observer runs. *)
Inductive process_world_steps operation parent child :
    ProcessWorld->list process_event->ProcessWorld->Prop :=
| process_world_nil : forall world,process_world_steps operation parent child world [] world
| process_world_cons : forall before observed event middle events after,
    ProcessInterference parent child before observed ->operation parent observed event middle ->
    process_world_steps operation parent child middle events after ->
    process_world_steps operation parent child before(event::events)after.

Lemma process_world_split operation parent child before prefix suffix after :
  process_world_steps operation parent child before(prefix++suffix)after ->
  exists middle,process_world_steps operation parent child before prefix middle /\
    process_world_steps operation parent child middle suffix after.
Proof.
  revert before;induction prefix as[|event rest IH];intros before RUN;cbn in RUN.
  - exists before;split;[constructor|exact RUN].
  - inversion RUN as[|first observed current middle tail last INTERFERENCE STEP TAIL];subst.
    destruct(IH _ TAIL)as[boundary[PREFIX SUFFIX]].
    exists boundary;split;[econstructor;eassumption|exact SUFFIX].
Qed.

Theorem process_trace_retains_incarnation operation (linux:LinuxProcessContract operation)
    parent child before events after :
  OwnsUnreaped before parent child ->Forall(fun event=>process_nonreaping event=true)events ->
  process_world_steps operation parent child before events after ->OwnsUnreaped after parent child.
Proof.
  intros OWNER EVENTS RUN;revert OWNER EVENTS;induction RUN;intros OWNER EVENTS;[exact OWNER|].
  inversion EVENTS;subst;apply IHRUN;[|assumption].
  eapply(linux_nonreaping_owner _ linux);[|eassumption|exact H0].
  eapply unreaped_owner_survives_interference;[exact OWNER|exact H].
Qed.

Lemma interference_files parent child before after :
  ProcessInterference parent child before after ->
  process_cgroup_files after parent=process_cgroup_files before parent.
Proof. intro INTERFERENCE;destruct INTERFERENCE;assumption. Qed.

Lemma interference_owned_scope parent child before after :
  OwnsUnreaped before parent child ->ProcessInterference parent child before after ->
  owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child).
Proof.
  intros[PID[OWNER[REAP SOLE]]]INTERFERENCE.
  destruct INTERFERENCE as[old new PIDFRAME PARENTFRAME GROUPFRAME PHASEFRAME FILEFRAME REAPFRAME SOLEFRAME|
    old new pid replacement FREE NUMBER NEW PIDFRAME TASKFRAME FILEFRAME REAPFRAME SOLEFRAME].
  - exact GROUPFRAME.
  - rewrite TASKFRAME;[reflexivity|intro SAME;subst replacement;congruence].
Qed.

Theorem process_trace_retains_file operation (linux:LinuxProcessContract operation)
    parent child before events after :
  Forall(fun event=>process_file_frame_event event=true)events ->
  process_world_steps operation parent child before events after ->
  process_cgroup_files after parent=process_cgroup_files before parent.
Proof.
  intros EVENTS RUN;revert EVENTS;induction RUN;intros EVENTS;[reflexivity|].
  inversion EVENTS;subst;rewrite(IHRUN H4).
  erewrite(linux_fixed_file_frame _ linux);[|eassumption|exact H0].
  eapply interference_files;exact H.
Qed.

Definition process_quiet_event event :=
  process_nonreaping event &&
    match event with process_entry(entry_library(original_event(io_step _ _)))=>false|_=>true end.

Lemma quiet_scope_frame before parent event :
  process_quiet_event event=true ->process_scope_frame_event before parent event.
Proof.
  unfold process_quiet_event,process_scope_frame_event;rewrite Bool.andb_true_iff.
  intros[NONREAP QUIET];split;[exact NONREAP|].
  destruct event;try exact I;destruct event;try exact I;destruct event;try exact I;
    destruct ev;try exact I;discriminate.
Qed.

Theorem process_trace_retains_scope operation (linux:LinuxProcessContract operation)
    parent child before events after :
  OwnsUnreaped before parent child ->Forall(fun event=>process_quiet_event event=true)events ->
  process_world_steps operation parent child before events after ->
  OwnsUnreaped after parent child /\
    owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child).
Proof.
  intros OWNER EVENTS RUN;revert OWNER EVENTS;induction RUN;intros OWNER EVENTS;[auto|].
  inversion EVENTS;subst.
  assert(OBSERVED:OwnsUnreaped observed parent child)
    by(eapply unreaped_owner_survives_interference;[exact OWNER|exact H]).
  assert(FRAME:process_scope_frame_event observed parent event)by(apply quiet_scope_frame;assumption).
  assert(MIDDLE:OwnsUnreaped middle parent child)
    by(eapply(linux_nonreaping_owner _ linux);[exact OBSERVED|exact(proj1 FRAME)|exact H0]).
  destruct(IHRUN MIDDLE H4)as[AFTER GROUP];split;[exact AFTER|].
  rewrite GROUP,(linux_passive_scope_frame _ linux _ _ _ _ _ OBSERVED FRAME H0).
  eapply interference_owned_scope;[exact OWNER|exact H].
Qed.
