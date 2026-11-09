(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Both source branches consume one non-CLONE_FILES fork transaction. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths
  NamespaceBorrow NamespaceMemory NamespaceObjects NamespaceKernel NamespaceTraceRegion
  NamespaceChildResult NamespaceChildTail NamespaceForkPrefix.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

(* A successful Linux fork copies the virtual memory and descriptor table at
   this one call. Each branch may update its own errno cell. The actual source
   continuation, channel selection, stores and branch calls are proved below. *)
Record NativeForkCopy cell before parent child : Prop := {
  fork_parent_copy : entry_errno_partial cell before parent;
  fork_child_copy : entry_errno_partial cell before child;
  fork_parent_errno : entry_errno_ready cell parent;
  fork_child_errno : entry_errno_ready cell child
}.

Theorem one_fork_produces_both_source_returns ge cell world snapshot before parent child k :
  fork_matches world snapshot ->NativeForkCopy cell before parent child ->
  namespace_step ge cell(live(Callstate namespace_fork_definition[]k before))
    (namespace_forked(task_pid(fork_child snapshot)))
    (live(Returnstate(Vint(task_pid(fork_child snapshot)))k parent)) /\
  namespace_step ge cell(live(Callstate namespace_fork_definition[]k before))
    (namespace_forked Int.zero)(live(Returnstate(Vint Int.zero)k child)) /\
  namespace_fork_effect world snapshot(task_pid(fork_child snapshot))world /\
  namespace_fork_effect world snapshot Int.zero(namespace_fork_child world snapshot).
Proof.
  intros MATCH[COPY_PARENT COPY_CHILD ERRNO_PARENT ERRNO_CHILD].
  repeat split;[apply namespace_fork_step|apply namespace_fork_step|
    apply namespace_fork_parent_effect|apply namespace_fork_child_effect];assumption.
Qed.

Theorem lost_fork_acknowledgement_can_still_create_child ge cell world snapshot before parent child k :
  fork_matches world snapshot ->NativeForkCopy cell before parent child ->
  namespace_step ge cell(live(Callstate namespace_fork_definition[]k before))
    namespace_fork_lost(dead parent) /\
  namespace_step ge cell(live(Callstate namespace_fork_definition[]k before))
    (namespace_forked Int.zero)(live(Returnstate(Vint Int.zero)k child)) /\
  namespace_kernel_event world namespace_fork_lost(namespace_fork_child world snapshot).
Proof.
  intros MATCH[COPY_PARENT COPY_CHILD ERRNO_PARENT ERRNO_CHILD].
  split;[apply namespace_fork_loss;assumption|].
  split;[apply namespace_fork_step;assumption|].
  eapply namespace_kernel_fork_lost_created;apply namespace_fork_child_effect;exact MATCH.
Qed.

Theorem one_source_fork_has_both_certified_tails scope first second failure reply le before
    world snapshot parent child :
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  fork_matches world snapshot ->NativeForkCopy(scope_cell scope)before parent child ->
  namespace_step namespace_ge(scope_cell scope)
    (live(Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before))
    (namespace_forked(task_pid(fork_child snapshot)))
    (live(Returnstate(Vint(task_pid(fork_child snapshot)))
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))parent)) /\
  namespace_step namespace_ge(scope_cell scope)
    (live(Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before))
    (namespace_forked Int.zero)
    (live(Returnstate(Vint Int.zero)
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child)) /\
  namespace_fork_effect world snapshot(task_pid(fork_child snapshot))world /\
  namespace_fork_effect world snapshot Int.zero(namespace_fork_child world snapshot) /\
  namespace_trace_region namespace_ge(scope_cell scope)(ChildResult scope)16
    (child_fork_log scope first second failure reply(task_pid(fork_child snapshot)))
    (Returnstate(Vint(task_pid(fork_child snapshot)))
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))parent) /\
  namespace_trace_region namespace_ge(scope_cell scope)(ChildResult scope)16
    (child_fork_log scope first second failure reply Int.zero)
    (Returnstate(Vint Int.zero)
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child).
Proof.
  intros FRONTIER MATCH COPY.
  destruct(one_fork_produces_both_source_returns namespace_ge(scope_cell scope)world snapshot
    before parent child(child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))
    MATCH COPY)as[PARENT[CHILD[PARENT_WORLD CHILD_WORLD]]].
  split;[exact PARENT|]. split;[exact CHILD|]. split;[exact PARENT_WORLD|]. split;[exact CHILD_WORLD|].
  inversion FRONTIER;subst;try discriminate.
  match goal with HISTORY:child_signal_log _ _ _ _ _=child_signal_log _ _ _ _ _|-_=>
    destruct(child_signal_log_injective _ _ _ _ _ _ _ _ _ HISTORY)as[FIRST[SECOND[FAILURE REPLY]]];
    subst end.
  destruct COPY as[COPY_PARENT COPY_CHILD ERRNO_PARENT ERRNO_CHILD].
  split;eapply child_fork_return_trace;try eassumption.
  all: try(eapply child_storage_partial;eassumption).
  all: try(eapply namespace_errno_effect_preserves_borrows;eassumption).
  all: eapply namespace_partial_preserves_load;try eassumption;
    match goal with SEP:child_storage_separate _ _|-_=>destruct SEP as[A[B REST]];exact B end.
Qed.
