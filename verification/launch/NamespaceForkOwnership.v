(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The actual common socket construction owns exactly one parent-endpoint slot. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceObjects NamespaceEndpoint NamespaceMachine NamespaceKernel NamespaceWorldTrace
  NamespaceForkWorld NamespaceForkInputs NamespacePaths NamespaceStructure NamespaceMemory NamespaceChildResult NamespaceForkPrefix NamespaceTraceRegion.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_channel_common_unique_parent before after output first second failure reply:
  0<=Int.signed failure ->
  namespace_kernel_steps before(child_channel_prefix_events output first second failure reply)after ->
  exists channel,namespace_table after first=Some(endpoint_binding channel parent_endpoint) /\
    namespace_table after failure=Some(endpoint_binding channel child_endpoint) /\
    unique_parent_endpoint(namespace_table after)channel first.
Proof.
  intros FAILURE RUN;unfold child_channel_prefix_events in RUN.
  inversion RUN;subst;clear RUN.
  match goal with PAIR:namespace_kernel_event _ (namespace_paired _ _ _ _ _ _ _ _) _|-_=>
    destruct(namespace_pair_kernel_details _ _ _ _ _ PAIR)as[channel[paired[PAIRTABLE[AMBIENT WORLD]]]];
    subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with DUP:namespace_kernel_event _ (namespace_duplicated _ _ _) _|-_=>
    destruct(namespace_duplicate_kernel_details _ _ _ _ FAILURE DUP)as[duplicated[DUPTABLE WORLD]];subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with CLOSE:namespace_kernel_event _ (namespace_process(process_entry(entry_library(close_returned _ _)))) _|-_=>
    destruct(namespace_close_kernel_details _ _ _ _ CLOSE)as[inherited[CLOSETABLE WORLD]];subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with MASK:namespace_kernel_event _ (namespace_masked _ _) _|-_=>
    pose proof(namespace_mask_kernel_details _ _ MASK)as WORLD;subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with DEFAULT:namespace_kernel_event _ (namespace_defaulted _ _) _|-_=>
    pose proof(namespace_default_kernel_details _ _ DEFAULT)as WORLD;subst end.
  match goal with REST:namespace_kernel_steps _ [] _|-_=>inversion REST;subst;clear REST end.
  cbn[namespace_retable]in DUPTABLE,CLOSETABLE.
  destruct(local_child_channel _ _ _ _ _ _ _ _ _ PAIRTABLE DUPTABLE CLOSETABLE)
    as[FIRST[SECOND[MINIMUM[PEER[CHILD CLOEXEC]]]]].
  exists channel;cbn[namespace_table namespace_retable namespace_remask namespace_default_action];
    cbn[namespace_table];split;[exact PEER|]. split;[exact CHILD|].
  eapply local_channel_has_unique_parent_endpoint;eassumption.
Qed.

Theorem actual_common_fork_unique_parent scope common before fork_world first second failure reply le memory channel:
  scope_history scope=[] ->
  ChildPrefixResult scope(namespace_fd_events common)
    (Clight.Callstate namespace_fork_definition[]
      (NamespacePaths.child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))memory) ->
  namespace_fd_events common=child_signal_log scope first second failure reply ->
  namespace_kernel_steps before common fork_world ->
  namespace_table fork_world first=Some(endpoint_binding channel parent_endpoint) ->
  unique_parent_endpoint(namespace_table fork_world)channel first.
Proof.
  intros HISTORY FRONTIER LOG KERNEL PEER.
  rewrite LOG in FRONTIER.
  destruct(NamespaceForkInputs.actual_common_fork_inputs _ _ _ _ _ _ _ FRONTIER)
    as[REGS[FAILURE[NONNEGATIVE REST]]].
  pose proof(namespace_kernel_filter_is_same_run _ _ _ KERNEL)as FILTERED.
  rewrite LOG in FILTERED.
  unfold child_signal_log,child_mask_log,child_closed_log,child_duplicate_log,child_pair_log in FILTERED.
  rewrite HISTORY in FILTERED;cbn in FILTERED.
  destruct(actual_channel_common_unique_parent _ _ _ _ _ _ _ NONNEGATIVE FILTERED)
    as[created[ACTUAL[CHILD UNIQUE]]].
  rewrite PEER in ACTUAL;unfold endpoint_binding in ACTUAL;inversion ACTUAL;subst created;exact UNIQUE.
Qed.
