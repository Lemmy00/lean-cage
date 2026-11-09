(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The source-selected guest consumes its own kernel fork/channel trace. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceTraceRegion
  NamespaceAllocation NamespaceMemory NamespacePaths NamespaceChildResult NamespaceWorldTrace.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_child_guest_has_private_fork scope events endpoint before_world after_world failure k m :
  scope_history scope=[] ->
  ChildResult scope(namespace_fd_events events)endpoint ->
  endpoint=Callstate(Ctypes.Internal f_guest)
    [Vint(scope_input scope);Vint(scope_output scope);Vint(scope_errors scope);Vint failure]k m ->
  namespace_kernel_steps before_world events after_world ->
  handoff_borrowed_input(scope_cell scope)m(scope_borrowed scope) /\
  exists first channel snapshot,
    Mem.load Mint32 m(storage_peer(scope_storage scope))0=Some(Vint first) /\
    Mem.load Mint32 m(storage_pid(scope_storage scope))0=Some(Vint Int.zero) /\
    namespace_task after_world=fork_child snapshot /\
    namespace_parent after_world=Some(namespace_task before_world) /\
    namespace_table_identity after_world<>namespace_table_identity before_world /\
    namespace_sigchld after_world=default_signal_action /\
    namespace_signal_mask after_world=namespace_blockable_mask Int64.mone /\
    namespace_table after_world first=Some(endpoint_binding channel parent_endpoint) /\
    namespace_table after_world failure=Some(endpoint_binding channel child_endpoint) /\
    parent_channel_cloexec(namespace_table after_world)channel /\
    60<=Int.signed failure /\
    Forall(fun outside=>channel_absent outside channel)(namespace_ambient after_world).
Proof.
  intros HISTORY RESULT FRONTIER KERNEL;subst endpoint.
  inversion RESULT;subst;try discriminate.
  match goal with LOG:child_fork_log _ _ _ _ _ _=namespace_fd_events events|-_=>
    pose proof(namespace_kernel_filter_is_same_run _ _ _ KERNEL)as OBSERVED;
    rewrite <-LOG in OBSERVED;
    unfold child_fork_log,child_signal_log,child_mask_log,child_closed_log,
      child_duplicate_log,child_pair_log in OBSERVED;
    rewrite HISTORY in OBSERVED;cbn in OBSERVED end.
  match goal with NONNEGATIVE:0<=Int.signed failure|-_=>
    destruct(selected_child_same_run_ownership _ _ _ _ _ _ _ NONNEGATIVE OBSERVED)
      as[channel[snapshot OWNED]] end.
  split;[assumption|]. exists first,channel,snapshot.
  split;[assumption|]. split;[assumption|exact OWNED].
Qed.
