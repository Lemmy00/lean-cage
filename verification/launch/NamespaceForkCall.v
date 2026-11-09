(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual caller allocation and call lead to one shared fork frontier. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From EntryNative Require Import EntrySource NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths
  NamespaceMemory NamespaceTraceRegion NamespaceChildResult NamespaceChildCall NamespacePrepared NamespaceForkPrefix.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Theorem child_call_common_fork_prefix request before :
  handoff_borrowed_input(request_cell request)before(request_borrowed request) ->
  Mem.range_perm before(request_peer request)0 4 Cur Freeable ->
  Mem.range_perm before(request_pid request)0 4 Cur Freeable ->
  request_peer request<>request_pid request ->request_peer request<>tls_block(request_cell request) ->
  request_pid request<>tls_block(request_cell request) ->
  ~In(request_peer request)(handoff_borrowed_blocks(request_borrowed request)) ->
  ~In(request_pid request)(handoff_borrowed_blocks(request_borrowed request)) ->
  exists pair,~Mem.valid_block before pair /\
    namespace_trace_region namespace_ge(request_cell request)(ChildPrefixResult(request_scope request pair))
      110(request_history request)
      (Callstate(Internal f_create_entry_child)(child_values(request_arguments request))
        (request_continuation request)before).
Proof.
  eapply child_call_allocates_and_certifies_to.
  intros pair after;apply child_pre_fork_body_certificate.
Qed.

Theorem prepared_namespace_common_fork_prefix before prepared cell borrowed
    input output errors le k history :
  Mem.valid_block before(tls_block cell) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  handoff_borrowed_input cell prepared borrowed ->
  (forall object position kind permission,
    Mem.perm(namespace_initial_memory before)object position kind permission ->
    Mem.perm prepared object position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->
  le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  exists peer pid pair,
    namespace_trace_region namespace_ge cell
      (ChildPrefixResult{|scope_cell:=cell;
        scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
        scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
        scope_continuation:=NamespaceCaller.namespace_creation_cont(namespace_initial_env before)le k;
        scope_history:=history|})114 history
      (State f_namespace_init(NamespaceCaller.namespace_tail 9)k(namespace_initial_env before)le prepared).
Proof.
  intros TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR.
  destruct(namespace_entry_owns_child_outputs before cell borrowed TLS BLOCKS)
    as[peer[pid[PEER[PID[PEER_OWNED[PID_OWNED[DISTINCT[PEER_TLS[PID_TLS[PEER_PRIVATE PID_PRIVATE]]]]]]]]]].
  set(request:={|request_cell:=cell;request_borrowed:=borrowed;request_input:=input;
    request_output:=output;request_errors:=errors;request_peer:=peer;request_pid:=pid;
    request_continuation:=NamespaceCaller.namespace_creation_cont(namespace_initial_env before)le k;
    request_history:=history|}).
  destruct(child_call_common_fork_prefix request prepared INPUT
    ltac:(intros position RANGE;apply PERMISSIONS;apply PEER_OWNED;lia)
    ltac:(intros position RANGE;apply PERMISSIONS;apply PID_OWNED;exact RANGE)
    DISTINCT PEER_TLS PID_TLS PEER_PRIVATE PID_PRIVATE)as[pair[FRESH CERT]].
  exists peer,pid,pair.
  eapply namespace_trace_store_path with(count:=4%nat)(remaining:=110%nat).
  - eapply NamespaceCaller.namespace_create_call_source;eauto.
  - exact CERT.
Qed.
