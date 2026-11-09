(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: One-operation Linux contracts connect source returns to object ownership. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects.
Import ListNotations.
Open Scope Z_scope.

Record SignalAction := {
  action_handler : int64;
  action_flags : int64;
  action_restorer : int64;
  action_mask : int64
}.
Definition default_signal_action :=
  {|action_handler:=Int64.zero;action_flags:=Int64.zero;
    action_restorer:=Int64.zero;action_mask:=Int64.zero|}.

Record NamespaceWorld := {
  namespace_task : TaskIdentity;
  namespace_parent : option TaskIdentity;
  namespace_table_identity : nat;
  namespace_table : DescriptorTable;
  namespace_ambient : list DescriptorTable;
  namespace_sigchld : SignalAction;
  namespace_signal_mask : int64
}.

Definition namespace_retable world table :=
  {|namespace_task := namespace_task world;namespace_parent := namespace_parent world;
    namespace_table_identity := namespace_table_identity world;namespace_table := table;
    namespace_ambient := namespace_ambient world;
    namespace_sigchld := namespace_sigchld world;
    namespace_signal_mask := namespace_signal_mask world|}.

Definition namespace_remask world mask :=
  {|namespace_task := namespace_task world;namespace_parent := namespace_parent world;
    namespace_table_identity := namespace_table_identity world;namespace_table := namespace_table world;
    namespace_ambient := namespace_ambient world;
    namespace_sigchld := namespace_sigchld world;
    namespace_signal_mask := mask|}.

Definition namespace_fork_child world (snapshot : ForkSnapshot) :=
  {|namespace_task := fork_child snapshot;namespace_parent := Some (namespace_task world);
    namespace_table_identity := fork_child_table_identity snapshot;
    namespace_table := namespace_table world;namespace_ambient := namespace_ambient world;
    namespace_sigchld := namespace_sigchld world;
    namespace_signal_mask := namespace_signal_mask world|}.

(* An exec resets caught handlers; an already-default SIGCHLD action remains
   default. Other incoming actions are deliberately left unconstrained here. *)
Definition namespace_exec world action :=
  {|namespace_task:=namespace_task world;namespace_parent:=namespace_parent world;
    namespace_table_identity:=namespace_table_identity world;
    namespace_table:=exec_table(namespace_table world);namespace_ambient:=namespace_ambient world;
    namespace_sigchld:=action;namespace_signal_mask:=namespace_signal_mask world|}.
Definition namespace_exec_action before after :=
  namespace_sigchld before=default_signal_action -> after=default_signal_action.

(* The snapshot is the paired result of one non-CLONE_FILES Linux fork.
   Both returned branches use this same snapshot. No application descriptor
   selection, argument construction or branch decision is part of this law. *)
Definition fork_matches world snapshot :=
  fork_parent snapshot = namespace_task world /\
  fork_parent_table_identity snapshot = namespace_table_identity world /\
  fork_inherited_table snapshot = namespace_table world.

Inductive namespace_fork_effect world snapshot : int -> NamespaceWorld -> Prop :=
| namespace_fork_parent_effect :
    fork_matches world snapshot ->
    namespace_fork_effect world snapshot (task_pid (fork_child snapshot)) world
| namespace_fork_child_effect :
    fork_matches world snapshot ->
    namespace_fork_effect world snapshot Int.zero (namespace_fork_child world snapshot).

(* SIGKILL and SIGSTOP cannot be blocked by rt_sigprocmask. *)
Definition namespace_blockable_mask mask :=
  Int64.and mask (Int64.not (Int64.or (Int64.repr 256) (Int64.repr 262144))).

Definition namespace_default_action world signal :=
  if Int.eq signal (Int.repr 17) then
    {|namespace_task:=namespace_task world;namespace_parent:=namespace_parent world;
      namespace_table_identity:=namespace_table_identity world;namespace_table:=namespace_table world;
      namespace_ambient:=namespace_ambient world;namespace_sigchld:=default_signal_action;
      namespace_signal_mask:=namespace_signal_mask world|}
  else world.

Definition namespace_passive_event event :=
  match event with
  | namespace_process (process_waited _ _ _ _ _) |
    namespace_process (process_traced _ _ _ _ _) |
    namespace_process (process_wait_lost _ _ _ _) |
    namespace_process (process_trace_lost _ _ _ _) |
    namespace_process (process_clocked _ _ _ _) | namespace_process (process_clock_lost _ _ _) |
    namespace_process (process_auxiliary _) |
    namespace_process process_waiting => true
  | namespace_process (process_entry entry) =>
      match entry with
      | entry_formatted _ _ _ _ | entry_format_lost _ _ _ |
        entry_exec_returned _ _ _ _ | entry_exec_lost _ _ _ | entry_primitive_wait => true
      | entry_library library =>
          match library with close_returned _ _ | exit_requested _ => false | _ => true end
      | _ => false
      end
  | namespace_waiting => true
  | _ => false
  end.

Definition namespace_flags_bit flags := negb (Int.eq (Int.and flags Int.one) Int.zero).

Inductive namespace_kernel_event : NamespaceWorld -> namespace_event -> NamespaceWorld -> Prop :=
| namespace_kernel_pair_success : forall before output offset first second channel after,
    socketpair_table (namespace_table before) first second channel after ->
    Forall (fun table=>channel_absent table channel) (namespace_ambient before) ->
    namespace_kernel_event before
      (namespace_paired (Int.repr 1) (Int.repr 524289) Int.zero output offset Int.zero first second)
      (namespace_retable before after)
| namespace_kernel_pair_failure : forall before output offset first second,
    namespace_kernel_event before
      (namespace_paired (Int.repr 1) (Int.repr 524289) Int.zero output offset Int.mone first second) before
| namespace_kernel_duplicate_success : forall before source minimum result after,
    duplicate_table (namespace_table before) source minimum result after ->
    namespace_kernel_event before (namespace_duplicated source minimum result)
      (namespace_retable before after)
| namespace_kernel_duplicate_failure : forall before source minimum,
    namespace_kernel_event before (namespace_duplicated source minimum Int.mone) before
| namespace_kernel_mask_success : forall before mask,
    namespace_kernel_event before (namespace_masked mask Int64.zero)
      (namespace_remask before (namespace_blockable_mask mask))
| namespace_kernel_mask_failure : forall before mask,
    namespace_kernel_event before (namespace_masked mask Int64.mone) before
| namespace_kernel_default_success : forall before signal,
    namespace_kernel_event before (namespace_defaulted signal Int64.zero)
      (namespace_default_action before signal)
| namespace_kernel_default_failure : forall before signal,
    namespace_kernel_event before (namespace_defaulted signal Int64.mone) before
| namespace_kernel_fork_success : forall before snapshot returned after,
    namespace_fork_effect before snapshot returned after ->
    namespace_kernel_event before (namespace_forked returned) after
| namespace_kernel_fork_failure : forall before,
    namespace_kernel_event before (namespace_forked Int.mone) before
| namespace_kernel_close : forall before descriptor reply after,
    close_table (namespace_table before) descriptor reply after ->
    namespace_kernel_event before
      (namespace_process (process_entry (entry_library (close_returned descriptor reply))))
      (namespace_retable before after)
| namespace_kernel_flags_zero : forall before descriptor,
    namespace_kernel_event before
      (namespace_process (process_entry (entry_flags_returned descriptor Int.zero Int.zero)))
      (namespace_retable before (descriptor_flags (namespace_table before) descriptor false))
| namespace_kernel_flags_one : forall before descriptor,
    namespace_kernel_event before
      (namespace_process (process_entry (entry_flags_returned descriptor Int.one Int.zero)))
      (namespace_retable before (descriptor_flags (namespace_table before) descriptor true))
| namespace_kernel_flags_failure : forall before descriptor flags,
    namespace_kernel_event before
      (namespace_process (process_entry (entry_flags_returned descriptor flags Int.mone))) before
| namespace_kernel_exec : forall before path arguments environment action,
    namespace_exec_action before action ->
    namespace_kernel_event before
      (namespace_process (process_entry (entry_image path arguments environment)))
      (namespace_exec before action)
| namespace_kernel_source : forall before trace,
    namespace_kernel_event before
      (namespace_process (process_entry (entry_library (original_event (source_step trace))))) before
| namespace_kernel_errno : forall before,
    namespace_kernel_event before
      (namespace_process (process_entry (entry_library (original_event errno_step)))) before
| namespace_kernel_wait : forall before,
    namespace_kernel_event before namespace_waiting before
| namespace_kernel_passive : forall before event,
    namespace_passive_event event = true -> namespace_kernel_event before event before
| namespace_kernel_exit : forall before code,
    namespace_kernel_event before
      (namespace_process (process_entry (entry_library (exit_requested code))))
      (namespace_retable before (fun _=>None))
| namespace_kernel_flags_lost_unchanged : forall before descriptor flags,
    namespace_kernel_event before
      (namespace_process (process_entry (entry_flags_lost descriptor flags))) before
| namespace_kernel_flags_lost_applied : forall before descriptor flags,
    namespace_kernel_event before
      (namespace_process (process_entry (entry_flags_lost descriptor flags)))
      (namespace_retable before
        (descriptor_flags (namespace_table before) descriptor (namespace_flags_bit flags)))
| namespace_kernel_pair_lost_unchanged : forall before output offset,
    namespace_kernel_event before
      (namespace_pair_lost (Int.repr 1) (Int.repr 524289) Int.zero output offset) before
| namespace_kernel_pair_lost_created : forall before output offset first second channel after,
    socketpair_table (namespace_table before) first second channel after ->
    Forall (fun table=>channel_absent table channel) (namespace_ambient before) ->
    namespace_kernel_event before
      (namespace_pair_lost (Int.repr 1) (Int.repr 524289) Int.zero output offset)
      (namespace_retable before after)
| namespace_kernel_duplicate_lost_unchanged : forall before descriptor minimum,
    namespace_kernel_event before (namespace_duplicate_lost descriptor minimum) before
| namespace_kernel_duplicate_lost_created : forall before source minimum result after,
    duplicate_table (namespace_table before) source minimum result after ->
    namespace_kernel_event before (namespace_duplicate_lost source minimum)
      (namespace_retable before after)
| namespace_kernel_fork_lost_unchanged : forall before,
    namespace_kernel_event before namespace_fork_lost before
| namespace_kernel_fork_lost_created : forall before snapshot returned after,
    namespace_fork_effect before snapshot returned after ->
    namespace_kernel_event before namespace_fork_lost after
| namespace_kernel_mask_lost_unchanged : forall before mask,
    namespace_kernel_event before (namespace_mask_lost mask) before
| namespace_kernel_mask_lost_applied : forall before mask,
    namespace_kernel_event before (namespace_mask_lost mask)
      (namespace_remask before (namespace_blockable_mask mask))
| namespace_kernel_default_lost_unchanged : forall before signal,
    namespace_kernel_event before (namespace_default_lost signal) before
| namespace_kernel_default_lost_applied : forall before signal,
    namespace_kernel_event before (namespace_default_lost signal)
      (namespace_default_action before signal).

Theorem actual_fork_child_has_owned_table world snapshot returned after :
  namespace_fork_effect world snapshot returned after -> returned = Int.zero ->
  namespace_task after = fork_child snapshot /\
  namespace_parent after = Some (namespace_task world) /\
  namespace_table after = namespace_table world /\
  namespace_table_identity after <> namespace_table_identity world /\
  namespace_task after <> namespace_task world.
Proof.
  intros FORK ZERO.
  assert (NONZERO : task_pid (fork_child snapshot) <> Int.zero).
  { intro SAME; pose proof (fork_child_positive snapshot) as POSITIVE;
      rewrite SAME,Int.signed_zero in POSITIVE; lia. }
  inversion FORK; subst.
  - exfalso; apply NONZERO; congruence.
  - destruct H as [PARENT [TABLE CONTENTS]].
    cbn [namespace_fork_child]; repeat split; try reflexivity.
    + rewrite <- TABLE; intro SAME; apply (fork_different_tables snapshot); symmetry; exact SAME.
    + rewrite <- PARENT; intro SAME; apply (fork_different_tasks snapshot); symmetry; exact SAME.
Qed.

Theorem actual_fork_parent_observes_child_pid world snapshot returned after :
  namespace_fork_effect world snapshot returned after -> returned <> Int.zero ->
  returned = task_pid (fork_child snapshot) /\ after = world /\
  fork_parent snapshot = namespace_task world.
Proof.
  intros FORK NONZERO; inversion FORK; subst; [destruct H; auto|contradiction].
Qed.

Theorem source_selected_child_has_real_parent ge cell before k memory snapshot after_world after_memory :
  namespace_fork_effect before snapshot Int.zero after_world ->
  entry_errno_partial cell memory after_memory -> entry_errno_ready cell after_memory ->
  namespace_step ge cell (live (Callstate namespace_fork_definition [] k memory))
    (namespace_forked Int.zero) (live (Returnstate (Vint Int.zero) k after_memory)) /\
  namespace_parent after_world = Some (namespace_task before) /\
  namespace_table after_world = namespace_table before /\
  namespace_table_identity after_world <> namespace_table_identity before.
Proof.
  intros FORK FRAME ERRNO.
  destruct (actual_fork_child_has_owned_table _ _ _ _ FORK eq_refl)
    as [TASK [PARENT [TABLE [PRIVATE DIFFERENT]]]].
  split; [apply namespace_fork_step; assumption|auto].
Qed.

Theorem namespace_kernel_ambient_frame before event after :
  namespace_kernel_event before event after -> namespace_ambient after = namespace_ambient before.
Proof.
  intro STEP; inversion STEP; subst; cbn; auto.
  all: try (unfold namespace_default_action; destruct (Int.eq signal (Int.repr 17)); reflexivity).
  all: match goal with FORK : namespace_fork_effect _ _ _ _ |- _ => inversion FORK; subst; reflexivity end.
Qed.

Theorem observed_sigchld_action_is_default before after :
  namespace_kernel_event before (namespace_defaulted (Int.repr 17) Int64.zero) after ->
  namespace_sigchld after = default_signal_action.
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  unfold namespace_default_action; rewrite Int.eq_true; reflexivity.
Qed.

Theorem namespace_socketpair_is_globally_fresh before after output offset first second :
  namespace_kernel_event before
    (namespace_paired (Int.repr 1) (Int.repr 524289) Int.zero output offset Int.zero first second) after ->
  exists channel,
    socketpair_table (namespace_table before) first second channel (namespace_table after) /\
    Forall (fun table=>channel_absent table channel) (namespace_ambient after).
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  exists channel; cbn; auto.
Qed.

Theorem kernel_fork_child_pid_is_fresh world snapshot returned after :
  namespace_fork_effect world snapshot returned after ->
  task_pid (fork_child snapshot) <> task_pid (namespace_task world).
Proof.
  intro FORK; inversion FORK; subst; destruct H as [PARENT REST]; rewrite <- PARENT.
  all: intro SAME; apply (fork_different_pids snapshot); symmetry; exact SAME.
Qed.
