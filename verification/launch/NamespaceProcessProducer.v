(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Lease the same fork incarnation selected by the actual namespace source. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Machine.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceTraceRegion
  NamespaceMemory NamespaceChildResult NamespaceWorldTrace NamespaceParent.
From EntryProcess Require Import ProcessOwnership ProcessPhysicalTrace.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_parent_source_produces_unreaped scope events before_world after_world m child :
  scope_history scope=[] ->
  ChildResult scope(namespace_fd_events events)
    (Returnstate(Vint Int.zero)(call_cont(scope_continuation scope))m) ->
  Mem.load Mint32 m(storage_pid(scope_storage scope))0=Some(Vint child) ->0<=Int.signed child ->
  namespace_kernel_steps before_world events after_world ->
  exists first second failure reply snapshot inherited fork_world,
    child=task_pid(fork_child snapshot) /\fork_parent snapshot=namespace_task before_world /\
    namespace_kernel_steps before_world(child_channel_events(storage_pair(scope_storage scope))
      first second failure reply child)fork_world /\
    namespace_fork_effect(child_fork_world before_world inherited)snapshot child fork_world /\
    namespace_sigchld(child_fork_world before_world inherited)=default_signal_action /\
    namespace_signal_mask(child_fork_world before_world inherited)=namespace_blockable_mask Int64.mone /\
    (forall process_before process_after,
      ForkProcessEffect(child_fork_world before_world inherited)process_before snapshot process_after ->
      process_sole_waiter process_before(fork_parent snapshot)=true ->
      OwnsUnreaped process_after(fork_parent snapshot)(fork_child snapshot)).
Proof.
  intros HISTORY RESULT PID NONNEGATIVE RUN.
  destruct(actual_parent_return_has_fork_receipt _ _ _ _ _ _ HISTORY RESULT PID NONNEGATIVE RUN)
    as[INPUT RECEIPT].
  destruct RECEIPT as[first [second [failure [reply [channel [snapshot [inherited [fork_world RECEIPT]]]]]]]].
  destruct RECEIPT as[PEER[CHILD[PARENT[PREFIX[FORK[DEFAULT[MASK REST]]]]]]].
  exists first,second,failure,reply,snapshot,inherited,fork_world.
  split;[exact CHILD|]. split;[exact PARENT|]. split;[exact PREFIX|]. split;[exact FORK|].
  split;[exact DEFAULT|]. split;[exact MASK|].
  intros process_before process_after EFFECT SOLE.
  eapply source_default_fork_produces_unreaped;[exact EFFECT|exact DEFAULT|exact SOLE].
Qed.
