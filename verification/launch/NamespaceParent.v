(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The parent admission PID comes from this source execution's own fork. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceTraceRegion
  NamespaceAllocation NamespaceMemory NamespacePaths NamespaceChildResult NamespaceWorldTrace.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_parent_return_has_fork_receipt scope events before_world after_world m child :
  scope_history scope=[] ->
  ChildResult scope(namespace_fd_events events)
    (Returnstate(Vint Int.zero)(call_cont(scope_continuation scope))m) ->
  Mem.load Mint32 m(storage_pid(scope_storage scope))0=Some(Vint child) ->0<=Int.signed child ->
  namespace_kernel_steps before_world events after_world ->
  handoff_borrowed_input(scope_cell scope)m(scope_borrowed scope) /\
  exists first second failure reply channel snapshot inherited fork_world,
    Mem.load Mint32 m(storage_peer(scope_storage scope))0=Some(Vint first) /\
    child=task_pid(fork_child snapshot) /\fork_parent snapshot=namespace_task before_world /\
    namespace_kernel_steps before_world(child_channel_events(storage_pair(scope_storage scope))
      first second failure reply child)fork_world /\
    namespace_fork_effect(child_fork_world before_world inherited)snapshot child fork_world /\
    namespace_sigchld(child_fork_world before_world inherited)=default_signal_action /\
    namespace_signal_mask(child_fork_world before_world inherited)=namespace_blockable_mask Int64.mone /\
    60<=Int.signed failure /\
    inherited first=Some(endpoint_binding channel parent_endpoint) /\
    inherited failure=Some(endpoint_binding channel child_endpoint) /\
    parent_channel_cloexec inherited channel /\
    Forall(fun outside=>channel_absent outside channel)(namespace_ambient before_world).
Proof.
  intros HISTORY RESULT PID NONNEGATIVE KERNEL.
  inversion RESULT;subst;try discriminate.
  - match goal with RANGE:1<=Int.signed Int.zero<=4095|-_=>rewrite Int.signed_zero in RANGE;lia end.
  - match goal with OLD:Mem.load Mint32 m(storage_pid(scope_storage scope))0=Some(Vint ?returned)|-_=>
      assert(returned=child)by congruence;subst returned end.
    match goal with LOG:child_parent_log _ _ _ _ _ _ _=namespace_fd_events events|-_=>
      pose proof(namespace_kernel_filter_is_same_run _ _ _ KERNEL)as OBSERVED;
      rewrite <-LOG in OBSERVED;
      unfold child_parent_log,child_fork_log,child_signal_log,child_mask_log,child_closed_log,
        child_duplicate_log,child_pair_log in OBSERVED;
      rewrite HISTORY in OBSERVED;cbn in OBSERVED end.
    change(namespace_kernel_steps before_world
      (child_channel_events(storage_pair(scope_storage scope)) first second failure reply child++
        [namespace_process(ProcessMachine.process_entry(entry_library(close_returned failure closed)))])after_world)
      in OBSERVED.
    destruct(namespace_kernel_steps_split _ _ _ _ OBSERVED)as[fork_world[PREFIX CLOSE]].
    destruct(child_channel_same_run_kernel_producer before_world fork_world
      (storage_pair(scope_storage scope)) first second failure reply child H2 NONNEGATIVE PREFIX)
      as[channel[snapshot[inherited[FORK[DEFAULT[MASK[D0[D1[MINIMUM[FIRST[ENDPOINT[CLOEXEC AMBIENT]]]]]]]]]]]].
    destruct(actual_fork_parent_observes_child_pid _ _ _ _ FORK H1)
      as[CHILD[WORLD PARENT]].
    split;[assumption|]. exists first,second,failure,reply,channel,snapshot,inherited,fork_world.
    split;[assumption|]. split;[exact CHILD|]. split.
    + unfold child_fork_world,namespace_default_action in PARENT;rewrite Int.eq_true in PARENT;exact PARENT.
    + split;[exact PREFIX|]. split;[exact FORK|]. split;[exact DEFAULT|]. split;[exact MASK|].
      split;[exact MINIMUM|]. split;[exact FIRST|]. split;[exact ENDPOINT|]. split;assumption.
Qed.
