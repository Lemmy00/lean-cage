(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The zero return of one actual fork reaches its own guest image. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput NativeHandoffArguments.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceMemory
  NamespaceRegion NamespaceTraceRegion NamespaceChildResult NamespaceForkPrefix NamespaceFork
  NamespaceObjects NamespaceKernel NamespaceWorldTrace NamespaceGuestFlags.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Definition namespace_fork_words := flat_map(fun event=>
  match event with namespace_forked returned=>[returned]|_=>[] end).

Lemma child_fork_log_length scope first second failure reply returned:
  length(child_fork_log scope first second failure reply returned)=(length(scope_history scope)+6)%nat.
Proof.
  unfold child_fork_log,child_signal_log,child_mask_log,child_closed_log,child_duplicate_log,child_pair_log.
  repeat rewrite length_app;cbn;lia.
Qed.

Lemma actual_zero_fork_result_is_guest scope first second failure reply events endpoint:
  scope_history scope=[] ->
  ChildResult scope(child_fork_log scope first second failure reply Int.zero++namespace_fd_events events)endpoint ->
  namespace_fd_events events=[] /\exists le memory,
    endpoint=Callstate(Internal f_guest)
      [Vint(scope_input scope);Vint(scope_output scope);Vint(scope_errors scope);Vint failure]
      (child_guest_cont(storage_pair(scope_storage scope))le(scope_continuation scope))memory /\
    handoff_borrowed_input(scope_cell scope)memory(scope_borrowed scope) /\0<=Int.signed failure.
Proof.
  intros HISTORY RESULT.
  remember(child_fork_log scope first second failure reply Int.zero++namespace_fd_events events)as observed eqn:LOG.
  destruct RESULT as[log error memory RANGE BORROWED BEFORE|
    a b fd closed le memory REGISTERS FAILURE NONNEGATIVE BORROWED PEER PID|
    a b fd closed child tail memory NONZERO NONNEGATIVE BORROWED PEER PID].
  - destruct BEFORE as[suffix[SAME FORKFREE]].
    assert(MEMBER:In(namespace_forked Int.zero)log).
    { rewrite LOG;apply in_or_app;left;unfold child_fork_log;apply in_or_app;right;left;reflexivity. }
    rewrite SAME,HISTORY in MEMBER;cbn in MEMBER.
    apply Forall_forall with(x:=namespace_forked Int.zero)in FORKFREE;[contradiction|exact MEMBER].
  - assert(EMPTY:namespace_fd_events events=[]).
    { apply length_zero_iff_nil.
      pose proof(f_equal(@length namespace_event)LOG)as LENGTH.
      rewrite length_app,!child_fork_log_length in LENGTH;lia. }
    rewrite EMPTY,app_nil_r in LOG;unfold child_fork_log in LOG;apply app_inv_tail in LOG.
    destruct(child_signal_log_injective _ _ _ _ _ _ _ _ _ LOG)as[A[B[FD CLOSED]]].
    subst a b fd closed;split;[exact EMPTY|];exists le,memory;auto.
  - pose proof(f_equal namespace_fork_words LOG)as FORKS.
    unfold namespace_fork_words,child_parent_log,child_fork_log,child_signal_log,child_mask_log,
      child_closed_log,child_duplicate_log,child_pair_log in FORKS.
    rewrite HISTORY in FORKS;cbn in FORKS;repeat rewrite flat_map_app in FORKS;cbn in FORKS.
    inversion FORKS;congruence.
Qed.

Theorem actual_child_branch_image_reaches_guest scope first second failure reply le before
    world snapshot parent child events target path arguments environment:
  scope_history scope=[] ->
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  fork_matches world snapshot ->NativeForkCopy(scope_cell scope)before parent child ->
  namespace_steps namespace_ge(scope_cell scope)
    (live(Returnstate(Vint Int.zero)
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child))events target ->
  In(namespace_guest_event(entry_image path arguments environment))events ->
  exists prefix rest guest_le memory,
    events=prefix++rest /\namespace_fd_events prefix=[] /\namespace_no_images prefix /\
    namespace_steps namespace_ge(scope_cell scope)
      (live(Returnstate(Vint Int.zero)
        (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child))prefix
      (live(Callstate(Internal f_guest)
        [Vint(scope_input scope);Vint(scope_output scope);Vint(scope_errors scope);Vint failure]
        (child_guest_cont(storage_pair(scope_storage scope))guest_le(scope_continuation scope))memory)) /\
    handoff_borrowed_input(scope_cell scope)memory(scope_borrowed scope) /\
    0<=Int.signed failure /\
    namespace_steps namespace_ge(scope_cell scope)
      (live(Callstate(Internal f_guest)
        [Vint(scope_input scope);Vint(scope_output scope);Vint(scope_errors scope);Vint failure]
        (child_guest_cont(storage_pair(scope_storage scope))guest_le(scope_continuation scope))memory))rest target /\
    In(namespace_guest_event(entry_image path arguments environment))rest.
Proof.
  intros HISTORY FRONTIER MATCH COPY RUN IMAGE.
  destruct(one_source_fork_has_both_certified_tails scope first second failure reply le before world snapshot parent child
    FRONTIER MATCH COPY)as[PARENT[CHILD[PARENT_WORLD[CHILD_WORLD[PARENT_CERT CHILD_CERT]]]]].
  destruct(namespace_trace_execution_split _ _ _ _ _ _ CHILD_CERT _ _ RUN)
    as[[COST[NOIMAGE RESIDUAL]]|[prefix[endpoint[rest[EVENTS[COST[NOIMAGES[PRE[RESULT POST]]]]]]]]].
  - apply Forall_forall with(x:=namespace_guest_event(entry_image path arguments environment))in NOIMAGE;
      [discriminate|exact IMAGE].
  - destruct(actual_zero_fork_result_is_guest _ _ _ _ _ _ _ HISTORY RESULT)
      as[EMPTY[guest_le[memory[ENDPOINT[BORROWED NONNEGATIVE]]]]];subst endpoint.
    exists prefix,rest,guest_le,memory.
    split;[exact EVENTS|]. split;[exact EMPTY|]. split;[exact NOIMAGES|].
    split;[exact PRE|]. split;[exact BORROWED|]. split;[exact NONNEGATIVE|]. split;[exact POST|].
    rewrite EVENTS in IMAGE;apply in_app_iff in IMAGE;destruct IMAGE as[EARLY|LATER];[|exact LATER].
    apply Forall_forall with(x:=namespace_guest_event(entry_image path arguments environment))in NOIMAGES;
      [discriminate|exact EARLY].
Qed.

Theorem child_guest_prefix_preserves_fork_world before events after:
  namespace_fd_events events=[] ->namespace_kernel_steps before events after ->after=before.
Proof.
  intros EMPTY RUN;pose proof(namespace_kernel_filter_is_same_run _ _ _ RUN)as FILTERED.
  rewrite EMPTY in FILTERED;inversion FILTERED;reflexivity.
Qed.
