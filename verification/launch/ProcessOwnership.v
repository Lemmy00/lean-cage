(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.provenance: Explicit individual Linux operations act on the fork-owned incarnation. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessStatus.
From EntryNamespace Require Import NamespaceObjects.
From LeanCageMainNumber Require Import NumberMath.
Import ListNotations.
Open Scope Z_scope.

Inductive TaskPhase := task_running | task_traced_stop | task_exited.

Definition process_machine_event event := process_entry(entry_library(original_event event)).

Record OwnedTaskView := {
  owned_parent : TaskIdentity;
  owned_phase : TaskPhase;
  owned_tracer : option TaskIdentity;
  owned_options : int64;
  owned_cgroup : option nat
}.

(* A PID slot and a kernel task identity are different objects. The map may
   change after a reap; the application must retain its unreaped-child token. *)
Record ProcessWorld := {
  process_pid : int -> option TaskIdentity;
  process_tasks : TaskIdentity -> OwnedTaskView;
  process_cgroup_files : TaskIdentity -> int -> option nat;
  process_explicit_reap : TaskIdentity -> bool;
  process_sole_waiter : TaskIdentity -> bool
}.

Definition OwnsUnreaped (world:ProcessWorld) (parent child:TaskIdentity) :=
  process_pid world (task_pid child)=Some child /\
    owned_parent (process_tasks world child)=parent /\ process_explicit_reap world parent=true /\
    process_sole_waiter world parent=true.

Definition OwnsStopped world parent child :=
  OwnsUnreaped world parent child /\
  owned_phase(process_tasks world child)=task_traced_stop /\
  owned_tracer(process_tasks world child)=Some parent.

Definition canonical_pid (bytes:list Byte.int) (child:TaskIdentity) :=
  Forall decimal_digit_ok bytes /\
  (exists first rest,bytes=first::rest /\first<>Byte.repr 48) /\
  decimal_number bytes=Some(Int.signed(task_pid child)).

(* A failed wait never reaps; a stopped status never reaps. Loss has no later
   live source state, so it deliberately does not transport a live lease. *)
Definition process_nonreaping event :=
  match event with
  | process_waited _ _ _ _ (wait_failed _) => true
  | process_waited _ _ _ _ (wait_status _ word) => admission_is_stopped word
  | process_traced _ _ _ _ _ | process_waiting | process_clocked _ _ _ _ => true
  | process_auxiliary(auxiliary_returned _ _ _ _) => true
  | process_entry entry =>
      match entry with
      | entry_library library =>
          match library with
          | original_event loss_step | original_event(partial_loss _ _ _) |
            memcpy_lost _ _ _ _ | exit_requested _ => false
          | _=>true
          end
      | entry_formatted _ _ _ _ | entry_flags_returned _ _ _ |
        entry_exec_returned _ _ _ _ | entry_primitive_wait => true
      | _=>false
      end
  | _=>false
  end.

Definition process_file_frame_event event :=
  match event with
  | process_entry(entry_library(close_returned _ _)) => false
  | _=>process_nonreaping event
  end.

Definition process_scope_frame_event before parent event :=
  process_nonreaping event=true /\
  match event with
  | process_entry(entry_library(original_event(io_step request _))) =>
      process_cgroup_files before parent(IO.descriptor request)=None
  | _=>True
  end.

(* These are Linux/runtime laws for a single genuine operation. In particular,
   the cgroup law does not construct argv, choose the FD/PID, run write_all,
   authorize a caller, or claim that the application has admitted a workload. *)
Record LinuxProcessContract (operation:TaskIdentity->ProcessWorld->process_event->ProcessWorld->Prop) : Prop := {
  linux_nonreaping_owner : forall before after parent child event,
    OwnsUnreaped before parent child ->process_nonreaping event=true ->
    operation parent before event after ->OwnsUnreaped after parent child;
  linux_fixed_file_frame : forall before after parent event,
    process_file_frame_event event=true ->operation parent before event after ->
    process_cgroup_files after parent=process_cgroup_files before parent;
  linux_passive_scope_frame : forall before after parent child event,
    OwnsUnreaped before parent child ->process_scope_frame_event before parent event ->
    operation parent before event after ->
    owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child);
  linux_source_owner : forall before after parent child trace,
    OwnsUnreaped before parent child ->
    operation parent before(process_machine_event(source_step trace))after ->
    OwnsUnreaped after parent child /\
      owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child) /\
      process_cgroup_files after parent=process_cgroup_files before parent;
  linux_errno_owner : forall before after parent child,
    OwnsUnreaped before parent child ->
    operation parent before(process_machine_event errno_step)after ->
    OwnsUnreaped after parent child /\
      owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child) /\
      process_cgroup_files after parent=process_cgroup_files before parent;
  linux_io_owner : forall before after parent child q reply,
    OwnsUnreaped before parent child ->
    operation parent before(process_machine_event(io_step q reply))after ->
    OwnsUnreaped after parent child /\
      process_cgroup_files after parent=process_cgroup_files before parent;
  linux_io_other_scope : forall before after parent child q reply,
    OwnsUnreaped before parent child -> process_cgroup_files before parent(IO.descriptor q)=None ->
    operation parent before(process_machine_event(io_step q reply))after ->
    owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child);
  linux_wait_sigstop : forall before after parent child status offset word,
    OwnsUnreaped before parent child ->
    operation parent before
      (process_waited(task_pid child)status offset Int.zero(wait_status(task_pid child)word))after ->
    admission_is_stopped word=true -> admission_is_sigstop word=true ->
    OwnsStopped after parent child;
  linux_wait_eintr : forall before after parent child status offset,
    OwnsUnreaped before parent child ->
    operation parent before
      (process_waited(task_pid child)status offset Int.zero(wait_failed(Int.repr 4)))after ->
    OwnsUnreaped after parent child;
  linux_cgroup_count : forall before after parent q bytes error group,
    IO.operation q=writing ->
    process_cgroup_files before parent(IO.descriptor q)=Some group ->
    operation parent before(process_machine_event(io_step q(transfer bytes error)))after ->
    Z.of_nat(length bytes)=requested q;
  linux_cgroup_move : forall before after parent child q bytes error group,
    OwnsUnreaped before parent child -> IO.operation q=writing ->
    process_cgroup_files before parent(IO.descriptor q)=Some group ->
    canonical_pid bytes child ->
    operation parent before(process_machine_event(io_step q(transfer bytes error)))after ->
    OwnsUnreaped after parent child /\ owned_cgroup(process_tasks after child)=Some group;
  linux_ptrace_options : forall before after parent child options,
    OwnsUnreaped before parent child ->
    operation parent before(process_traced(Int.repr 16896)(task_pid child)
      (Vlong Int64.zero)(Vlong options)Int64.zero)after ->
    OwnsStopped before parent child /\ OwnsStopped after parent child /\
      owned_options(process_tasks after child)=options /\
      owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child);
  linux_ptrace_continue : forall before after parent child,
    OwnsUnreaped before parent child ->
    operation parent before(process_traced(Int.repr 7)(task_pid child)
      (Vlong Int64.zero)(Vlong Int64.zero)Int64.zero)after ->
    OwnsStopped before parent child /\
      OwnsUnreaped after parent child /\ owned_phase(process_tasks after child)=task_running /\
      owned_tracer(process_tasks after child)=Some parent /\
      owned_options(process_tasks after child)=owned_options(process_tasks before child) /\
      owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child)
}.

(* Killing an unreaped child cannot recycle its PID. Once reaped, this relation
   permits a different incarnation with the same numeric PID. Source failure
   control, rather than a platform prohibition on reuse, excludes that path. *)
Inductive ProcessInterference (parent child:TaskIdentity) : ProcessWorld -> ProcessWorld -> Prop :=
| process_interference_frame : forall before after,
    process_pid after(task_pid child)=process_pid before(task_pid child) ->
    owned_parent(process_tasks after child)=owned_parent(process_tasks before child) ->
    owned_cgroup(process_tasks after child)=owned_cgroup(process_tasks before child) ->
    (owned_phase(process_tasks before child)=task_exited ->
      owned_phase(process_tasks after child)=task_exited) ->
    process_cgroup_files after parent=process_cgroup_files before parent ->
    process_explicit_reap after parent=process_explicit_reap before parent ->
    process_sole_waiter after parent=process_sole_waiter before parent ->
    ProcessInterference parent child before after
| process_interference_reuse : forall before after pid replacement,
    process_pid before pid=None -> task_pid replacement=pid ->
    process_pid after pid=Some replacement ->
    (forall other,other<>pid -> process_pid after other=process_pid before other) ->
    (child<>replacement -> process_tasks after child=process_tasks before child) ->
    process_cgroup_files after parent=process_cgroup_files before parent ->
    process_explicit_reap after parent=process_explicit_reap before parent ->
    process_sole_waiter after parent=process_sole_waiter before parent ->
    ProcessInterference parent child before after.

Theorem unreaped_incarnation_is_unique world parent child other :
  OwnsUnreaped world parent child -> process_pid world(task_pid child)=Some other -> other=child.
Proof. intros[BOUND[OWNER[REAPER SOLE]]] OTHER; congruence. Qed.

Theorem reaped_child_has_no_owner world parent child :
  process_pid world(task_pid child)=None -> ~OwnsUnreaped world parent child.
Proof. intros REAPED[OWNED[PARENT[REAPER SOLE]]];congruence. Qed.

Theorem reused_pid_is_not_old_child world parent old replacement :
  old<>replacement -> process_pid world(task_pid old)=Some replacement ->
  ~OwnsUnreaped world parent old.
Proof. intros DIFFERENT REUSED[OWNED[PARENT[REAPER SOLE]]];congruence. Qed.

Theorem unreaped_owner_survives_interference before after parent child :
  OwnsUnreaped before parent child -> ProcessInterference parent child before after ->
  OwnsUnreaped after parent child.
Proof.
  intros[BOUND[OWNER[REAPER SOLE]]] INTERFERENCE.
  destruct INTERFERENCE as[old new PIDFRAME PARENTFRAME GROUPFRAME PHASEFRAME FILEFRAME REAPFRAME SOLEFRAME|
    old new pid replacement FREE NUMBER NEW PIDFRAME TASKFRAME FILEFRAME REAPFRAME SOLEFRAME].
  - split;[rewrite PIDFRAME;exact BOUND|]. split.
    + rewrite PARENTFRAME;exact OWNER.
    + split;[rewrite REAPFRAME;exact REAPER|rewrite SOLEFRAME;exact SOLE].
  - assert(DIFFERENT:task_pid child<>pid)by(congruence).
    split;[rewrite PIDFRAME by exact DIFFERENT;exact BOUND|].
    split.
    + rewrite TASKFRAME;[exact OWNER|intro SAME;subst replacement;congruence].
    + split;[rewrite REAPFRAME;exact REAPER|rewrite SOLEFRAME;exact SOLE].
Qed.

Theorem matching_stop_refines_owned_fork operation (linux:LinuxProcessContract operation)
    before after snapshot status offset word :
  OwnsUnreaped before(fork_parent snapshot)(fork_child snapshot) ->
  operation (fork_parent snapshot) before(process_waited(task_pid(fork_child snapshot))status offset Int.zero
    (wait_status(task_pid(fork_child snapshot))word))after ->
  admission_is_stopped word=true -> admission_is_sigstop word=true ->
  OwnsStopped after(fork_parent snapshot)(fork_child snapshot).
Proof. intros; eapply linux_wait_sigstop; eassumption. Qed.

Theorem source_pid_write_establishes_membership operation (linux:LinuxProcessContract operation)
    before after parent child q bytes error group :
  OwnsUnreaped before parent child -> IO.operation q=writing ->
  process_cgroup_files before parent(IO.descriptor q)=Some group ->
  canonical_pid bytes child -> operation parent before(process_machine_event(io_step q(transfer bytes error)))after ->
  owned_cgroup(process_tasks after child)=Some group /\ OwnsUnreaped after parent child.
Proof.
  intros OWN WRITING FILE BYTES STEP.
  destruct(linux_cgroup_move _ linux _ _ _ _ _ _ _ _ OWN WRITING FILE BYTES STEP);auto.
Qed.

Theorem source_options_preserve_membership operation (linux:LinuxProcessContract operation)
    before after parent child group :
  OwnsUnreaped before parent child -> owned_cgroup(process_tasks before child)=Some group ->
  operation parent before(process_traced(Int.repr 16896)(task_pid child)(Vlong Int64.zero)
    (Vlong(Int64.repr 1048592))Int64.zero)after ->
  OwnsStopped after parent child /\ owned_options(process_tasks after child)=Int64.repr 1048592 /\
    owned_cgroup(process_tasks after child)=Some group.
Proof.
  intros OWN GROUP STEP.
  destruct(linux_ptrace_options _ linux _ _ _ _ _ OWN STEP)as[INITIAL[STOPPED[OPTIONS FRAME]]].
  split;[exact STOPPED|]. split;[exact OPTIONS|congruence].
Qed.

Theorem source_resume_preserves_setup operation (linux:LinuxProcessContract operation)
    before after parent child group :
  OwnsUnreaped before parent child -> owned_cgroup(process_tasks before child)=Some group ->
  owned_options(process_tasks before child)=Int64.repr 1048592 ->
  operation parent before(process_traced(Int.repr 7)(task_pid child)(Vlong Int64.zero)(Vlong Int64.zero)Int64.zero)after ->
  OwnsUnreaped after parent child /\ owned_phase(process_tasks after child)=task_running /\
    owned_tracer(process_tasks after child)=Some parent /\
    owned_options(process_tasks after child)=Int64.repr 1048592 /\
    owned_cgroup(process_tasks after child)=Some group.
Proof.
  intros OWN GROUP OPTIONS STEP.
  destruct(linux_ptrace_continue _ linux _ _ _ _ OWN STEP)as[INITIAL[BOUND[RUNNING[TRACER[OFRAME GFRAME]]]]].
  split;[exact BOUND|]. split;[exact RUNNING|]. split;[exact TRACER|]. split;congruence.
Qed.
