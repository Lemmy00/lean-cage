(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Construct the private channel once, at the common actual fork frontier. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps LibraryMachine ProcessEffects WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths
  NamespaceMemory NamespaceRegion NamespaceTraceRegion NamespaceChildResult NamespaceChildBody.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Lemma child_signal_log_injective scope first second failure reply first' second' failure' reply' :
  child_signal_log scope first second failure reply=child_signal_log scope first' second' failure' reply' ->
  first=first' /\second=second' /\failure=failure' /\reply=reply'.
Proof.
  unfold child_signal_log,child_mask_log,child_closed_log,child_duplicate_log,child_pair_log.
  repeat rewrite <-app_assoc;intro SAME;apply app_inv_head in SAME.
  inversion SAME;auto.
Qed.

Inductive ChildPrefixResult scope : list namespace_event -> Clight.state -> Prop :=
| child_prefix_error : forall log error after,
    1<=Int.signed error<=4095 ->
    handoff_borrowed_input(scope_cell scope)after(scope_borrowed scope) ->
    child_before_fork scope log ->
    ChildPrefixResult scope log
      (Returnstate(Vint error)(call_cont(scope_continuation scope))after)
| child_prefix_fork : forall first second failure reply le m,
    child_scope_registers scope le ->le!_failure=Some(Vint failure) ->0<=Int.signed failure ->
    child_storage_separate(scope_cell scope)(scope_storage scope) ->child_scope_private scope ->
    child_storage(scope_cell scope)(scope_storage scope)m ->
    handoff_borrowed_input(scope_cell scope)m(scope_borrowed scope) ->
    Mem.load Mint32 m(storage_peer(scope_storage scope))0=Some(Vint first) ->
    ChildPrefixResult scope(child_signal_log scope first second failure reply)
      (Callstate namespace_fork_definition []
        (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))m).

Theorem child_pre_fork_body_certificate scope le m :
  child_scope_registers scope le ->
  child_storage_separate(scope_cell scope)(scope_storage scope) ->child_scope_private scope ->
  child_storage(scope_cell scope)(scope_storage scope)m ->
  handoff_borrowed_input(scope_cell scope)m(scope_borrowed scope) ->
  namespace_trace_region namespace_ge(scope_cell scope)(ChildPrefixResult scope)109(scope_history scope)
    (State f_create_entry_child(fn_body f_create_entry_child)(scope_continuation scope)
      (child_env(storage_pair(scope_storage scope)))le m).
Proof.
  intros REGISTERS SEPARATE PRIVATE STORAGE BORROWED.
  eapply complete_child_body_trace_to;try eassumption.
  - intros;apply child_prefix_error;assumption.
  - intros temps memory first second failure reply REGS FAILURE NONNEGATIVE SEP PRIV OWN INPUT PEER.
    eapply namespace_trace_weaken with(n:=3%nat);[|lia].
    eapply namespace_trace_store_path with(count:=3%nat)(remaining:=0%nat).
    + apply child_fork_source.
    + apply namespace_trace_stop;eapply child_prefix_fork;eassumption.
Qed.

Theorem child_pre_fork_same_run scope le m events target :
  child_scope_registers scope le ->
  child_storage_separate(scope_cell scope)(scope_storage scope) ->child_scope_private scope ->
  child_storage(scope_cell scope)(scope_storage scope)m ->
  handoff_borrowed_input(scope_cell scope)m(scope_borrowed scope) ->
  namespace_steps namespace_ge(scope_cell scope)
    (live(State f_create_entry_child(fn_body f_create_entry_child)(scope_continuation scope)
      (child_env(storage_pair(scope_storage scope)))le m))events target ->
  ((namespace_cost events<=110)%nat /\namespace_no_images events /\
    (forall state,target=live state ->exists remaining,
      namespace_trace_region namespace_ge(scope_cell scope)(ChildPrefixResult scope)remaining
        (scope_history scope++namespace_fd_events events)state)) \/
  (exists prefix endpoint rest,events=prefix++rest /\namespace_no_images prefix /\
    namespace_steps namespace_ge(scope_cell scope)
      (live(State f_create_entry_child(fn_body f_create_entry_child)(scope_continuation scope)
        (child_env(storage_pair(scope_storage scope)))le m))prefix(live endpoint) /\
    ChildPrefixResult scope(scope_history scope++namespace_fd_events prefix)endpoint /\
    namespace_steps namespace_ge(scope_cell scope)(live endpoint)rest target).
Proof.
  intros REGISTERS SEPARATE PRIVATE STORAGE BORROWED RUN.
  destruct(namespace_trace_execution_split _ _ _ _ _ _
    (child_pre_fork_body_certificate scope le m REGISTERS SEPARATE PRIVATE STORAGE BORROWED)_ _ RUN)
    as[PREFIX|[prefix[endpoint[rest[EVENTS[COST[NOIMAGES[PRE[RESULT POST]]]]]]]]].
  - left;exact PREFIX.
  - right;exists prefix,endpoint,rest;auto.
Qed.
