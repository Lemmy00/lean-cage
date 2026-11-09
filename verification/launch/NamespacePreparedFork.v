(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The real prepared-root source prefix produces its selected common fork. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryProcess Require Import ProcessMachine ProcessCaller ProcessGlobalCalls ProcessPreparedOrigins ProcessJournal.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespaceCaller
  NamespacePaths NamespacePrepared NamespaceMemory NamespaceChildResult NamespaceForkPrefix NamespaceEffects
  NamespaceTraceRegion NamespaceRegion NamespacePostForkClosure NamespaceSourceFork NamespaceChildCall.
Import ListNotations.
Open Scope Z_scope.

Lemma prepared_fork_environment:namespace_ge=caller_ge.
Proof. reflexivity. Qed.
Local Opaque namespace_ge caller_ge.

Lemma prepared_child_result_has_no_fork scope log state:
  scope_history scope=[] ->ChildPrefixResult scope log state ->Forall before_local_fork log.
Proof.
  intros HISTORY RESULT;inversion RESULT;subst.
  - destruct H1 as[events[LOG FREE]];rewrite HISTORY in LOG;cbn in LOG;subst log;exact FREE.
  - unfold child_signal_log,child_mask_log,child_closed_log,child_duplicate_log,child_pair_log.
    rewrite HISTORY;cbn;repeat constructor;exact I.
Qed.

Theorem actual_common_fork_only_waits cell pair child_temps e le before events k memory:
  caller_env_global e ->
  namespace_steps namespace_ge cell
    (live(Callstate namespace_fork_definition[]
      (child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))before))events
    (live(Callstate namespace_fork_definition[]k memory)) ->
  k=child_fork_cont pair child_temps(namespace_creation_cont e le Kstop) /\memory=before /\
    namespace_fd_events events=[].
Proof.
  intro GLOBAL;revert before;induction events as[|event rest IH];intros before RUN.
  - inversion RUN;subst;repeat split;reflexivity.
  - inversion RUN as[|start current middle tail target STEP TAIL];subst.
    destruct(namespace_fork_cases _ _ _ _ _ _ STEP)
      as[[returned[after[PARTIAL[READY[EVENT TARGET]]]]]|[[EVENT TARGET]|
        [[after[PARTIAL[EVENT TARGET]]]|[EVENT TARGET]]]];subst event middle.
    + exfalso;eapply postfork_cannot_call_fork.
      * apply actual_fork_return_source_closed;exact GLOBAL.
      * rewrite prepared_fork_environment in TAIL;exact TAIL.
    + destruct(IH _ TAIL)as[K[MEMORY EMPTY]];split;[exact K|]. split;[exact MEMORY|].
      unfold namespace_fd_events in *;cbn;exact EMPTY.
    + destruct(namespace_dead_steps _ _ _ _ _ TAIL)as[EMPTY IMPOSSIBLE];discriminate.
    + destruct(namespace_dead_steps _ _ _ _ _ TAIL)as[EMPTY IMPOSSIBLE];discriminate.
Qed.

Lemma prepared_region_at_actual_fork scope n log before continuation returned after:
  scope_history scope=[] ->
  namespace_trace_region namespace_ge(scope_cell scope)(ChildPrefixResult scope)n log
    (Callstate namespace_fork_definition[]continuation before) ->
  namespace_step namespace_ge(scope_cell scope)
    (live(Callstate namespace_fork_definition[]continuation before))(namespace_forked returned)
    (live(Returnstate(Vint returned)continuation after)) ->
  ChildPrefixResult scope log(Callstate namespace_fork_definition[]continuation before).
Proof.
  intros HISTORY CERT STEP;inversion CERT as[count history state RESULT|count history state PROGRESS CASES];subst.
  - exact RESULT.
  - destruct(CASES _ _ STEP)as[[WAIT TARGET]|[[dead[TARGET NOIMAGE]]|
      [next[TARGET[ADV[NOIMAGE TAIL]]]]]];try discriminate.
    inversion TARGET;subst next.
    destruct(namespace_trace_actual _ _ _ _ _ _ TAIL)as[events[endpoint[RUN[COST[IMAGES RESULT]]]]].
    pose proof(prepared_child_result_has_no_fork _ _ _ HISTORY RESULT)as FREE.
    rewrite Forall_forall in FREE.
    specialize(FREE(namespace_forked returned)).
    exfalso;apply FREE.
    unfold namespace_advance;cbn[namespace_fd_event].
    apply in_or_app;left;apply in_or_app;right;cbn;auto.
Qed.

Lemma prepared_fd_events_append first second:
  namespace_fd_events(first++second)=namespace_fd_events first++namespace_fd_events second.
Proof. apply filter_app. Qed.

Theorem prepared_region_selected_fork scope e le n start events continuation before returned after:
  scope_history scope=[] ->scope_continuation scope=namespace_creation_cont e le Kstop ->caller_env_global e ->
  namespace_trace_region namespace_ge(scope_cell scope)(ChildPrefixResult scope)n[]start ->
  namespace_steps namespace_ge(scope_cell scope)(live start)events
    (live(Callstate namespace_fork_definition[]continuation before)) ->
  namespace_step namespace_ge(scope_cell scope)
    (live(Callstate namespace_fork_definition[]continuation before))(namespace_forked returned)
    (live(Returnstate(Vint returned)continuation after)) ->
  ChildPrefixResult scope(namespace_fd_events events)(Callstate namespace_fork_definition[]continuation before).
Proof.
  intros HISTORY CONTINUATION GLOBAL CERT RUN FORK.
  destruct(namespace_trace_execution_split _ _ _ _ _ _ CERT _ _ RUN)
    as[[COST[IMAGES RESIDUAL]]|[prefix[endpoint[rest[EVENTS[COST[IMAGES[PREFIX[RESULT SUFFIX]]]]]]]]].
  - destruct(RESIDUAL _ eq_refl)as[remaining REGION];cbn[app]in REGION.
    eapply prepared_region_at_actual_fork;[exact HISTORY|exact REGION|exact FORK].
  - cbn[app]in RESULT;pose proof RESULT as ORIGINAL.
    inversion RESULT as[history error memory RANGE BORROWED EARLY|
      first second failure reply temps memory REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE STORAGE BORROWED PEER];subst endpoint.
    + rewrite CONTINUATION in SUFFIX;cbn[call_cont]in SUFFIX.
      exfalso;eapply postfork_cannot_call_fork.
      * apply actual_creation_return_source_closed;exact GLOBAL.
      * rewrite prepared_fork_environment in SUFFIX;exact SUFFIX.
    + rewrite CONTINUATION in SUFFIX.
      destruct(actual_common_fork_only_waits _ _ _ _ _ _ _ _ _ GLOBAL SUFFIX)as[K[MEMORY EMPTY]].
      subst continuation before;rewrite EVENTS,prepared_fd_events_append,EMPTY,app_nil_r.
      rewrite CONTINUATION in ORIGINAL;exact ORIGINAL.
Qed.

Lemma prepared_canonical_env_form before:
  namespace_allocated_env(namespace_allocate_variables(fn_vars f_namespace_init)empty_env before)=namespace_initial_env before.
Proof. unfold namespace_initial_env,namespace_initial_allocation;reflexivity. Qed.
Lemma prepared_canonical_memory_form before:
  namespace_allocated_memory(namespace_allocate_variables(fn_vars f_namespace_init)empty_env before)=namespace_initial_memory before.
Proof. unfold namespace_initial_memory,namespace_initial_allocation;reflexivity. Qed.

Lemma prepared_canonical_env_global before:caller_env_global(namespace_initial_env before).
Proof.
  destruct(namespace_allocate_variables_source(fn_vars f_namespace_init)empty_env before)as[ALLOC OBJECTS].
  rewrite prepared_canonical_env_form,prepared_canonical_memory_form in ALLOC.
  rewrite prepared_fork_environment in ALLOC.
  exact(caller_namespace_allocated_environment _ _ _ ALLOC).
Qed.

(* Retain the allocation facts needed to build raw parent storage for this
   source scope. The global-content frame is supplied separately. *)
Theorem prepared_namespace_actual_scope before prepared cell borrowed input output errors le:
  Mem.valid_block before(tls_block cell) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  handoff_borrowed_input cell prepared borrowed ->
  (forall object position kind permission,Mem.perm(namespace_initial_memory before)object position kind permission ->
    Mem.perm prepared object position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->
  le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  exists peer pid pair,
    (namespace_initial_env before)!_pipefd=Some(peer,tarray tint 2) /\
    (namespace_initial_env before)!_child=Some(pid,tint) /\~Mem.valid_block prepared pair /\
    namespace_trace_region namespace_ge cell
      (ChildPrefixResult {|scope_cell:=cell;
        scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
        scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
        scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|})114[]
      (State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared).
Proof.
  intros TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR.
  destruct(namespace_entry_owns_child_outputs before cell borrowed TLS BLOCKS)
    as[peer[pid[PEER[PID[PEER_OWNED[PID_OWNED[DISTINCT[PEER_TLS[PID_TLS[PEER_PRIVATE PID_PRIVATE]]]]]]]]]].
  set(request:={|request_cell:=cell;request_borrowed:=borrowed;request_input:=input;
    request_output:=output;request_errors:=errors;request_peer:=peer;request_pid:=pid;
    request_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;request_history:=[]|}).
  destruct(child_call_allocates_and_certifies_to request
    (fun pair=>ChildPrefixResult(request_scope request pair))
    (fun pair after=>child_pre_fork_body_certificate(request_scope request pair)(child_parameters(request_arguments request))after)
    prepared INPUT
    ltac:(intros position RANGE;apply PERMISSIONS;apply PEER_OWNED;lia)
    ltac:(intros position RANGE;apply PERMISSIONS;apply PID_OWNED;exact RANGE)
    DISTINCT PEER_TLS PID_TLS PEER_PRIVATE PID_PRIVATE)as[pair[FRESH CERT]].
  exists peer,pid,pair;split;[exact PEER|]. split;[exact PID|]. split;[exact FRESH|].
  eapply namespace_trace_store_path with(count:=4%nat)(remaining:=110%nat).
  - eapply namespace_create_call_source;eauto.
  - exact CERT.
Qed.

Theorem actual_prepared_source_common_fork_owned(run:CallerSourceRun)returned(fork:ActualSourceFork run returned)
    before prepared borrowed input output errors le:
  source_before run=live(State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared) ->
  Mem.valid_block before(tls_block(source_cell run)) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  handoff_borrowed_input(source_cell run)prepared borrowed ->
  (forall object position kind permission,Mem.perm(namespace_initial_memory before)object position kind permission ->
    Mem.perm prepared object position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->
  le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  exists peer pid pair first second failure reply temps,
    let scope:={|scope_cell:=source_cell run;
      scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
      scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
      scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|} in
    (namespace_initial_env before)!_pipefd=Some(peer,tarray tint 2) /\
    (namespace_initial_env before)!_child=Some(pid,tint) /\~Mem.valid_block prepared pair /\
    source_fork_continuation _ _ fork=child_fork_cont pair temps(scope_continuation scope) /\
    namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply /\
    ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
      (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)).
Proof.
  intros START TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR.
  destruct(prepared_namespace_actual_scope before prepared(source_cell run)borrowed input output errors le
    TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR)as[peer[pid[pair[PEER[PID[FRESH CERT]]]]]].
  pose proof(source_fork_prefix _ _ fork)as PREFIX;rewrite START in PREFIX.
  rewrite <-prepared_fork_environment in PREFIX.
  pose proof(source_fork_operation _ _ fork)as FORK;rewrite <-prepared_fork_environment in FORK.
  pose(scope:={|scope_cell:=source_cell run;
    scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
    scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
    scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|}).
  pose proof(prepared_region_selected_fork scope(namespace_initial_env before)le _ _ _ _ _ _ _
    eq_refl eq_refl(prepared_canonical_env_global before)CERT PREFIX FORK)as FRONTIER.
  inversion FRONTIER as[log error memory RANGE BORROWED EARLY|
    first second failure reply temps memory REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE STORAGE BORROWED FIRST];subst.
  exists peer,pid,pair,first,second,failure,reply,temps;cbn zeta.
  split;[exact PEER|]. split;[exact PID|]. split;[exact FRESH|].
  split;[reflexivity|]. split;[reflexivity|]. rewrite H,H0;exact FRONTIER.
Qed.

Theorem actual_prepared_source_common_fork(run:CallerSourceRun)returned(fork:ActualSourceFork run returned)
    before prepared borrowed input output errors le:
  source_before run=live(State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared) ->
  Mem.valid_block before(tls_block(source_cell run)) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  handoff_borrowed_input(source_cell run)prepared borrowed ->
  (forall object position kind permission,Mem.perm(namespace_initial_memory before)object position kind permission ->
    Mem.perm prepared object position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->
  le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  exists peer pid pair first second failure reply temps,
    let scope:={|scope_cell:=source_cell run;
      scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
      scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
      scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|} in
    source_fork_continuation _ _ fork=child_fork_cont pair temps(scope_continuation scope) /\
    namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply /\
    ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
      (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)).
Proof.
  intros START TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR.
  destruct(prepared_namespace_calls_actual_common_fork before prepared(source_cell run)borrowed input output errors le Kstop[]
    TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR)as[peer[pid[pair CERT]]].
  pose proof(source_fork_prefix _ _ fork)as PREFIX;rewrite START in PREFIX.
  rewrite <-prepared_fork_environment in PREFIX.
  pose proof(source_fork_operation _ _ fork)as FORK;rewrite <-prepared_fork_environment in FORK.
  pose(scope:={|scope_cell:=source_cell run;
    scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
    scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
    scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|}).
  pose proof(prepared_region_selected_fork scope(namespace_initial_env before)le _ _ _ _ _ _ _
    eq_refl eq_refl(prepared_canonical_env_global before)CERT PREFIX FORK)as FRONTIER.
  inversion FRONTIER as[log error memory RANGE BORROWED EARLY|
    first second failure reply temps memory REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE STORAGE BORROWED PEER];subst.
  exists peer,pid,pair,first,second,failure,reply,temps;cbn zeta.
  split;[reflexivity|]. split;[reflexivity|]. rewrite H,H0;exact FRONTIER.
Qed.
