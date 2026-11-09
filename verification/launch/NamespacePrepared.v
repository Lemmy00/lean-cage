(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Derive caller cell ownership from the actual namespace function allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine FreshMemory StoreSteps.
From EntryNative Require Import EntrySource NativeHandoffArguments NativeHandoffInput.
From EntryProcess Require Import ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceStructure NamespaceAllocation NamespacePaths NamespaceCaller
  NamespaceBorrow NamespaceChildResult NamespaceChildCall NamespaceTraceRegion NamespaceForkPrefix.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge handoff_ge handoff_symbol.

Definition namespace_initial_allocation before :=
  namespace_allocate_variables(fn_vars f_namespace_init)empty_env before.
Definition namespace_initial_env before :=namespace_allocated_env(namespace_initial_allocation before).
Definition namespace_initial_memory before :=namespace_allocated_memory(namespace_initial_allocation before).

Theorem namespace_entry_owns_child_outputs before cell input :
  Mem.valid_block before(tls_block cell) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks input) ->
  exists peer pid,
    (namespace_initial_env before)!_pipefd=Some(peer,tarray tint 2) /\
    (namespace_initial_env before)!_child=Some(pid,tint) /\
    Mem.range_perm(namespace_initial_memory before)peer 0 8 Cur Freeable /\
    Mem.range_perm(namespace_initial_memory before)pid 0 4 Cur Freeable /\
    peer<>pid /\peer<>tls_block cell /\pid<>tls_block cell /\
    ~In peer(handoff_borrowed_blocks input) /\~In pid(handoff_borrowed_blocks input).
Proof.
  intros TLS BORROWED.
  destruct(namespace_owned_local_from_entry before _pipefd(tarray tint 2)ltac:(cbn;auto 12))
    as[peer[PEER[PEER_FRESH PEER_OWNED]]].
  destruct(namespace_owned_local_from_entry before _child tint ltac:(cbn;auto 12))
    as[pid[PID[PID_FRESH PID_OWNED]]].
  exists peer,pid;split;[exact PEER|]. split;[exact PID|].
  split;[exact PEER_OWNED|]. split;[exact PID_OWNED|].
  assert(DISTINCT:peer<>pid).
  { eapply(namespace_entry_has_distinct_local_objects before _pipefd _child);eauto;discriminate. }
  split;[exact DISTINCT|]. split;[intro SAME;apply PEER_FRESH;rewrite SAME;exact TLS|].
  split;[intro SAME;apply PID_FRESH;rewrite SAME;exact TLS|].
  split;intros MEMBER;rewrite Forall_forall in BORROWED;
    [apply PEER_FRESH|apply PID_FRESH];apply BORROWED;exact MEMBER.
Qed.

Theorem namespace_entry_callees_are_global before :
  (namespace_initial_env before)!_create_entry_child=None /\
  (namespace_initial_env before)!_admit_child=None /\
  (namespace_initial_env before)!_close=None /\
  (namespace_initial_env before)!_admission_cgroup=None /\
  (namespace_initial_env before)!_release_child=None /\
  (namespace_initial_env before)!_now_ms=None /\
  (namespace_initial_env before)!_send_frame=None /\
  (namespace_initial_env before)!_result_of=None /\
  (namespace_initial_env before)!_preflight=None.
Proof.
  unfold namespace_initial_env,namespace_initial_allocation;repeat split;
    rewrite namespace_allocate_away by(cbn;intuition discriminate);apply PTree.gempty.
Qed.

(* The root/identity/argument preparation producer supplies its actual frontier,
   its borrowed bytes, and the permission frame of its calls. It does not
   provide the local socketpair, alias separation, signal policy or fork. *)
Theorem prepared_namespace_calls_certified_child before prepared cell borrowed
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
      (ChildResult {|scope_cell:=cell;
        scope_storage:={|NamespaceMemory.storage_pair:=pair;NamespaceMemory.storage_peer:=peer;
          NamespaceMemory.storage_pid:=pid|};scope_borrowed:=borrowed;scope_input:=input;
        scope_output:=output;scope_errors:=errors;
        scope_continuation:=namespace_creation_cont(namespace_initial_env before)le k;
        scope_history:=history|})114 history
      (State f_namespace_init(namespace_tail 9)k(namespace_initial_env before)le prepared).
Proof.
  intros TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR.
  destruct(namespace_entry_owns_child_outputs before cell borrowed TLS BLOCKS)
    as[peer[pid[PEER[PID[PEER_OWNED[PID_OWNED[DISTINCT[PEER_TLS[PID_TLS[PEER_PRIVATE PID_PRIVATE]]]]]]]]]].
  set(request:={|request_cell:=cell;request_borrowed:=borrowed;request_input:=input;
    request_output:=output;request_errors:=errors;request_peer:=peer;request_pid:=pid;
    request_continuation:=namespace_creation_cont(namespace_initial_env before)le k;
    request_history:=history|}).
  destruct(child_call_allocates_and_certifies request prepared INPUT
    ltac:(intros position RANGE;apply PERMISSIONS;apply PEER_OWNED;lia)
    ltac:(intros position RANGE;apply PERMISSIONS;apply PID_OWNED;exact RANGE)
    DISTINCT PEER_TLS PID_TLS PEER_PRIVATE PID_PRIVATE)as[pair[FRESH CERT]].
  exists peer,pid,pair.
  eapply namespace_trace_store_path with(count:=4%nat)(remaining:=110%nat).
  - eapply namespace_create_call_source;eauto.
  - exact CERT.
Qed.


(* §AR-entry.caller: Recover the functional allocation from the actual source entry. *)
Theorem namespace_actual_allocation_determined variables initial before e after:
  alloc_variables namespace_ge initial before variables e after ->
  let result:=namespace_allocate_variables variables initial before in
  e=namespace_allocated_env result /\after=namespace_allocated_memory result.
Proof.
  intro ALLOCATION;induction ALLOCATION;cbn[namespace_allocate_variables].
  - split;reflexivity.
  - rewrite H;exact IHALLOCATION.
Qed.

Theorem actual_namespace_entry_allocation before arguments e le after:
  function_entry2 namespace_ge f_namespace_init arguments before e le after ->
  e=namespace_initial_env before /\after=namespace_initial_memory before.
Proof.
  intro ENTRY;inversion ENTRY;subst.
  match goal with ALLOC:alloc_variables _ empty_env before (fn_vars f_namespace_init)e after|-_=>
    exact(namespace_actual_allocation_determined _ _ _ _ _ ALLOC)end.
Qed.

Theorem actual_namespace_entry_globals before arguments e le after:
  function_entry2 namespace_ge f_namespace_init arguments before e le after ->caller_env_global e.
Proof.
  intro ENTRY;exact(caller_internal_entry_global f_namespace_init arguments before e le after
    ltac:(vm_compute;reflexivity)ENTRY).
Qed.

Definition namespace_old_env_fresh old(e:env):=
  forall id object ty,e!id=Some(object,ty)->~Mem.valid_block old object.

Theorem namespace_actual_allocation_fresh old variables initial before e after:
  alloc_variables namespace_ge initial before variables e after ->
  (forall object,Mem.valid_block old object->Mem.valid_block before object) ->
  namespace_old_env_fresh old initial ->namespace_old_env_fresh old e.
Proof.
  intro ALLOCATION;induction ALLOCATION as[initial before|initial before id ty variables middle object after e ALLOC REST IH];
    intros KEPT FRESH;[exact FRESH|].
  apply IH.
  - intros other VALID;eapply Mem.valid_block_alloc;[exact ALLOC|apply KEPT;exact VALID].
  - intros name current current_ty LOOKUP;destruct(peq name id)as[SAME|OTHER].
    + subst name;rewrite PTree.gss in LOOKUP;inversion LOOKUP;subst current.
      intro VALID;eapply Mem.fresh_block_alloc;[exact ALLOC|apply KEPT;exact VALID].
    + rewrite PTree.gso in LOOKUP by exact OTHER;exact(FRESH _ _ _ LOOKUP).
Qed.

Theorem actual_namespace_parent_local_separation before arguments e le after cell childobject pipe status:
  function_entry2 namespace_ge f_namespace_init arguments before e le after ->
  Mem.valid_block before(tls_block cell) ->
  Mem.valid_block before(namespace_symbol _admission_cgroup) ->
  Mem.valid_block before(namespace_symbol _preflight) ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->e!_status=Some(status,tint) ->
  childobject<>tls_block cell /\pipe<>tls_block cell /\status<>tls_block cell /\
    status<>childobject /\status<>pipe /\status<>namespace_symbol _admission_cgroup /\status<>namespace_symbol _preflight.
Proof.
  intros ENTRY TLS CGROUP PREFLIGHT CHILD PIPE STATUS.
  inversion ENTRY as[VARS NAMES DISJOINT ALLOC BIND];subst.
  assert(EMPTY_FRESH:namespace_old_env_fresh before empty_env).
  { intros id object ty LOOKUP;rewrite PTree.gempty in LOOKUP;discriminate. }
  pose proof(namespace_actual_allocation_fresh before _ _ _ _ _ ALLOC(fun object VALID=>VALID)EMPTY_FRESH)as FRESH.
  assert(EMPTY_VALID:namespace_env_valid before empty_env).
  { intros id object ty LOOKUP;rewrite PTree.gempty in LOOKUP;discriminate. }
  assert(EMPTY_INJECTIVE:namespace_env_injective empty_env).
  { intros id other object ty another other_ty LOOKUP;rewrite PTree.gempty in LOOKUP;discriminate. }
  pose proof(proj2(namespace_allocations_preserve_env_shape _ _ _ _ _ ALLOC EMPTY_VALID EMPTY_INJECTIVE))as INJECTIVE.
  repeat split.
  - intro SAME;apply(FRESH _ _ _ CHILD);rewrite SAME;exact TLS.
  - intro SAME;apply(FRESH _ _ _ PIPE);rewrite SAME;exact TLS.
  - intro SAME;apply(FRESH _ _ _ STATUS);rewrite SAME;exact TLS.
  - exact(INJECTIVE _status _child status tint childobject tint STATUS CHILD ltac:(discriminate)).
  - exact(INJECTIVE _status _pipefd status tint pipe(tarray tint 2)STATUS PIPE ltac:(discriminate)).
  - intro SAME;apply(FRESH _ _ _ STATUS);rewrite SAME;exact CGROUP.
  - intro SAME;apply(FRESH _ _ _ STATUS);rewrite SAME;exact PREFLIGHT.
Qed.


(* §AR-entry.caller: The prepared-root caller produces its common fork certificate. *)
Theorem prepared_namespace_calls_actual_common_fork before prepared cell borrowed
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
      (ChildPrefixResult {|scope_cell:=cell;
        scope_storage:={|NamespaceMemory.storage_pair:=pair;NamespaceMemory.storage_peer:=peer;
          NamespaceMemory.storage_pid:=pid|};scope_borrowed:=borrowed;scope_input:=input;
        scope_output:=output;scope_errors:=errors;
        scope_continuation:=namespace_creation_cont(namespace_initial_env before)le k;
        scope_history:=history|})114 history
      (State f_namespace_init(namespace_tail 9)k(namespace_initial_env before)le prepared).
Proof.
  intros TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR.
  destruct(namespace_entry_owns_child_outputs before cell borrowed TLS BLOCKS)
    as[peer[pid[PEER[PID[PEER_OWNED[PID_OWNED[DISTINCT[PEER_TLS[PID_TLS[PEER_PRIVATE PID_PRIVATE]]]]]]]]]].
  set(request:={|request_cell:=cell;request_borrowed:=borrowed;request_input:=input;
    request_output:=output;request_errors:=errors;request_peer:=peer;request_pid:=pid;
    request_continuation:=namespace_creation_cont(namespace_initial_env before)le k;
    request_history:=history|}).
  destruct(child_call_allocates_and_certifies_to request
    (fun pair=>ChildPrefixResult(request_scope request pair))
    (fun pair after=>child_pre_fork_body_certificate(request_scope request pair)(child_parameters(request_arguments request))after)
    prepared INPUT
    ltac:(intros position RANGE;apply PERMISSIONS;apply PEER_OWNED;lia)
    ltac:(intros position RANGE;apply PERMISSIONS;apply PID_OWNED;exact RANGE)
    DISTINCT PEER_TLS PID_TLS PEER_PRIVATE PID_PRIVATE)as[pair[FRESH CERT]].
  exists peer,pid,pair.
  eapply namespace_trace_store_path with(count:=4%nat)(remaining:=110%nat).
  - eapply namespace_create_call_source;eauto.
  - exact CERT.
Qed.
