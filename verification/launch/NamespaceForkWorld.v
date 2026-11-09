(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: The common source prefix supplies one fork world to both branches. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessOwnership ProcessPhysicalTrace.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace
  NamespaceTraceRegion NamespaceMemory NamespaceChildResult NamespaceForkPrefix NamespaceFork.
Import ListNotations.
Open Scope Z_scope.

Definition child_channel_prefix_events output first second failure reply :=
  [namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero output Ptrofs.zero Int.zero first second;
   namespace_duplicated second(Int.repr 60)failure;
   namespace_process(process_entry(entry_library(close_returned second reply)));
   namespace_masked Int64.mone Int64.zero;namespace_defaulted(Int.repr 17)Int64.zero].

Theorem child_channel_common_kernel_prefix before after output first second failure reply :
  0<=Int.signed failure ->
  namespace_kernel_steps before(child_channel_prefix_events output first second failure reply)after ->
  exists channel inherited,
    after=child_fork_world before inherited /\
    namespace_sigchld after=default_signal_action /\
    namespace_signal_mask after=namespace_blockable_mask Int64.mone /\
    first<>failure /\second<>failure /\60<=Int.signed failure /\
    inherited first=Some(endpoint_binding channel parent_endpoint) /\
    inherited failure=Some(endpoint_binding channel child_endpoint) /\
    parent_channel_cloexec inherited channel /\
    Forall(fun outside=>channel_absent outside channel)(namespace_ambient before) /\
    (forall descriptor binding,namespace_table before descriptor=Some binding ->
      inherited descriptor=Some binding /\descriptor_object binding<>release_endpoint channel parent_endpoint).
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
    as[FIRST_SECOND[SECOND_FAILURE[MINIMUM[FIRST[ENDPOINT CLOEXEC]]]]].
  assert(OLD:forall descriptor binding,namespace_table before descriptor=Some binding ->
    inherited descriptor=Some binding /\descriptor_object binding<>release_endpoint channel parent_endpoint).
  { intros descriptor binding BINDING;eapply local_channel_preserves_old_descriptors;eassumption. }
  exists channel,inherited;split;[reflexivity|].
  unfold namespace_default_action;rewrite Int.eq_true;cbn;auto 12.
Qed.

Theorem source_common_fork_world scope events before_world fork_world first second failure reply le memory :
  scope_history scope=[] ->
  ChildPrefixResult scope(namespace_fd_events events)
    (Callstate NamespaceMachine.namespace_fork_definition[]
      (NamespacePaths.child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))memory) ->
  namespace_fd_events events=child_signal_log scope first second failure reply ->
  namespace_kernel_steps before_world events fork_world ->
  exists channel inherited,
    fork_world=child_fork_world before_world inherited /\
    namespace_sigchld fork_world=default_signal_action /\
    namespace_signal_mask fork_world=namespace_blockable_mask Int64.mone /\
    first<>failure /\second<>failure /\60<=Int.signed failure /\
    inherited first=Some(endpoint_binding channel parent_endpoint) /\
    inherited failure=Some(endpoint_binding channel child_endpoint) /\
    parent_channel_cloexec inherited channel /\
    Forall(fun outside=>channel_absent outside channel)(namespace_ambient before_world) /\
    (forall descriptor binding,namespace_table before_world descriptor=Some binding ->
      inherited descriptor=Some binding /\descriptor_object binding<>release_endpoint channel parent_endpoint).
Proof.
  intros HISTORY FRONTIER LOG RUN.
  rewrite LOG in FRONTIER;inversion FRONTIER;subst;try discriminate.
  match goal with SAME:child_signal_log _ _ _ _ _=child_signal_log _ _ _ _ _|-_=>
    destruct(child_signal_log_injective _ _ _ _ _ _ _ _ _ SAME)as[FIRST[SECOND[FAILURE REPLY]]];subst end.
  eapply child_channel_common_kernel_prefix;[eassumption|].
  pose proof(namespace_kernel_filter_is_same_run _ _ _ RUN)as FILTERED.
  rewrite LOG in FILTERED.
  unfold child_signal_log,child_mask_log,child_closed_log,child_duplicate_log,child_pair_log in FILTERED.
  rewrite HISTORY in FILTERED;cbn in FILTERED;exact FILTERED.
Qed.

Theorem common_fork_has_one_explicit_reap_lease namespace process_before snapshot process_after :
  namespace_sigchld namespace=default_signal_action ->
  ForkProcessEffect namespace process_before snapshot process_after ->
  process_sole_waiter process_before(fork_parent snapshot)=true ->
  OwnsUnreaped process_after(fork_parent snapshot)(fork_child snapshot) /\
  namespace_fork_effect namespace snapshot(task_pid(fork_child snapshot))namespace /\
  namespace_fork_effect namespace snapshot Int.zero(namespace_fork_child namespace snapshot).
Proof.
  intros DEFAULT EFFECT SOLE.
  split;[eapply source_default_fork_produces_unreaped;eassumption|].
  split;[apply namespace_fork_parent_effect|apply namespace_fork_child_effect];
    exact(fork_process_matches _ _ _ _ EFFECT).
Qed.
