(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Preserve the actual global command descriptor through channel setup and fork. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber StoreSteps LibraryMachine ProcessEffects WriteAll FreshMemory ReceiverAllocation.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths NamespaceCaller
  NamespaceMemory NamespaceRegion NamespaceTraceRegion NamespaceTraceEffects NamespaceChildResult NamespaceForkPrefix
  NamespaceChildCall NamespacePrepared NamespacePreparedFork NamespaceEffects NamespaceBorrow.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge ProcessGlobalCalls.caller_ge EntrySource.prog.
Local Opaque namespace_allocate_variables namespace_allocated_env namespace_initial_env namespace_initial_allocation.

Definition prepared_setup_success event:=match event with
  |namespace_paired _ _ _ _ _ returned _ _=>returned=Int.zero
  |namespace_duplicated _ _ returned=>0<=Int.signed returned
  |namespace_masked _ returned|namespace_defaulted _ returned=>returned=Int64.zero
  |_=>True end.
Definition prepared_cgroup_result scope object value log state:Prop:=
  Forall before_local_fork log /\
    ((exists event,In event log /\~prepared_setup_success event) \/
     exists temps memory,state=Callstate namespace_fork_definition[]
       (child_fork_cont(storage_pair(scope_storage scope))temps(scope_continuation scope))memory /\
       Mem.load Mint32 memory object 0=Some value).

Lemma prepared_nonfork_log scope log:
  scope_history scope=[] ->child_before_fork scope log ->Forall before_local_fork log.
Proof. intros EMPTY[events[LOG FREE]];rewrite EMPTY in LOG;cbn in LOG;subst log;exact FREE. Qed.
Lemma prepared_nonfork_append log event:
  Forall before_local_fork log ->before_local_fork event ->Forall before_local_fork(log++[event]).
Proof. intros FREE EVENT;apply Forall_app;split;[exact FREE|constructor;[exact EVENT|constructor]]. Qed.
Lemma prepared_bad_last scope object value log event state:
  Forall before_local_fork log ->before_local_fork event ->~prepared_setup_success event ->
  prepared_cgroup_result scope object value(log++[event])state.
Proof.
  intros FREE NONFORK BAD;split;[apply prepared_nonfork_append;assumption|].
  left;exists event;split;[apply in_or_app;right;left;reflexivity|exact BAD].
Qed.
Lemma prepared_pair_frame cell before after pair offset returned first second object value:
  object<>tls_block cell ->object<>pair ->
  namespace_pair_effect cell pair offset before returned first second after ->
  Mem.load Mint32 before object 0=Some value ->Mem.load Mint32 after object 0=Some value.
Proof.
  intros TLS PAIR EFFECT LOAD;inversion EFFECT;subst.
  - eapply namespace_partial_preserves_load;eassumption.
  - eapply namespace_partial_preserves_load;[eassumption|exact TLS|].
    erewrite Mem.load_store_other;[|eassumption|left;exact PAIR].
    erewrite Mem.load_store_other;[exact LOAD|eassumption|left;exact PAIR].
Qed.

Section COMMON_BODY.
Variable scope:ChildScope.
Variable object:block.
Variable value:val.
Hypothesis HISTORY:scope_history scope=[].
Hypothesis OBJECT_TLS:object<>tls_block(scope_cell scope).
Hypothesis OBJECT_PAIR:object<>storage_pair(scope_storage scope).
Hypothesis OBJECT_PEER:object<>storage_peer(scope_storage scope).
Local Notation cell:=(scope_cell scope).
Local Notation objects:=(scope_storage scope).
Local Notation pair:=(storage_pair objects).
Local Notation k:=(scope_continuation scope).
Local Notation result:=(prepared_cgroup_result scope object value).

Lemma prepared_publish_peer_frame le memory first second failure reply:
  child_scope_registers scope le ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 26(child_signal_log scope first second failure reply)
    (State f_create_entry_child(child_tail 6(fn_body f_create_entry_child))k(child_env pair)le memory).
Proof.
  intros REGISTERS STORAGE FIRST LOAD.
  destruct(child_peer_store_exists _ _ _ first STORAGE)as[after STORE].
  assert(KEPT:Mem.load Mint32 after object 0=Some value).
  { erewrite Mem.load_store_other;[exact LOAD|exact STORE|left;exact OBJECT_PEER]. }
  eapply namespace_trace_weaken with(n:=9%nat);[|lia].
  eapply namespace_trace_store_path with(count:=6%nat)(remaining:=3%nat).
  - eapply child_publish_peer_source;[exact FIRST|exact(proj1(proj2(proj2(proj2 REGISTERS))))|exact STORE].
  - eapply namespace_trace_store_path with(count:=3%nat)(remaining:=0%nat).
    + apply child_fork_source.
    + apply namespace_trace_stop;split.
      * eapply prepared_nonfork_log;[exact HISTORY|].
        apply child_before_fork_extend;[apply child_mask_before_fork|exact I].
      * right;eexists;eexists;split;[reflexivity|exact KEPT].
Qed.

Lemma prepared_default_return_frame le memory first second failure reply returned:
  child_scope_registers scope le ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 60
    (child_mask_log scope first second failure reply++[namespace_defaulted(Int.repr 17)returned])
    (Returnstate(Vlong returned)(child_default_cont pair le k)memory).
Proof.
  intros REGISTERS STORAGE FIRST LOAD;destruct(Int64.eq_dec returned Int64.zero)as[ZERO|NONZERO].
  - subst returned;eapply namespace_trace_weaken with(n:=30%nat);[|lia].
    eapply namespace_trace_store_path with(count:=4%nat)(remaining:=26%nat).
    + apply child_default_success_source.
    + eapply prepared_publish_peer_frame;try eassumption;child_scope_registers.
  - apply namespace_trace_stop;apply prepared_bad_last;[|exact I|exact NONZERO].
    eapply prepared_nonfork_log;[exact HISTORY|apply child_mask_before_fork].
Qed.

Lemma prepared_default_tail_frame le memory first second failure reply:
  child_scope_registers scope le ->child_storage_separate cell objects ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 64(child_mask_log scope first second failure reply)
    (State f_create_entry_child(child_tail 5(fn_body f_create_entry_child))k(child_env pair)le memory).
Proof.
  intros REGISTERS SEPARATE STORAGE FIRST LOAD.
  eapply namespace_trace_store_path with(count:=3%nat)(remaining:=61%nat);[apply child_default_source|].
  eapply namespace_trace_default;[exact(proj1 STORAGE)|].
  intros returned after FRAME READY;eapply prepared_default_return_frame;try eassumption.
  - eapply child_storage_partial;eassumption.
  - eapply namespace_partial_preserves_load;[exact FRAME|exact(proj1 SEPARATE)|exact FIRST].
  - eapply namespace_partial_preserves_load;[exact FRAME|exact OBJECT_TLS|exact LOAD].
Qed.

Lemma prepared_mask_return_frame le memory first second failure reply returned:
  child_scope_registers scope le ->child_storage_separate cell objects ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 70
    (child_closed_log scope first second failure reply++[namespace_masked Int64.mone returned])
    (Returnstate(Vlong returned)(child_mask_cont pair le k)memory).
Proof.
  intros REGISTERS SEPARATE STORAGE FIRST LOAD;destruct(Int64.eq_dec returned Int64.zero)as[ZERO|NONZERO].
  - subst returned;eapply namespace_trace_weaken with(n:=68%nat);[|lia].
    eapply namespace_trace_store_path with(count:=4%nat)(remaining:=64%nat);[apply child_mask_success_source|].
    eapply prepared_default_tail_frame;try eassumption;child_scope_registers.
  - apply namespace_trace_stop;apply prepared_bad_last;[|exact I|exact NONZERO].
    eapply prepared_nonfork_log;[exact HISTORY|apply child_closed_before_fork].
Qed.

Lemma prepared_mask_tail_frame le memory first second failure reply:
  child_scope_registers scope le ->child_storage_separate cell objects ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 74(child_closed_log scope first second failure reply)
    (State f_create_entry_child(child_tail 4(fn_body f_create_entry_child))k(child_env pair)le memory).
Proof.
  intros REGISTERS SEPARATE STORAGE FIRST LOAD.
  eapply namespace_trace_store_path with(count:=3%nat)(remaining:=71%nat);[apply child_mask_source|].
  eapply namespace_trace_mask;[exact(proj1 STORAGE)|].
  intros returned after FRAME READY;eapply prepared_mask_return_frame;try eassumption.
  - eapply child_storage_partial;eassumption.
  - eapply namespace_partial_preserves_load;[exact FRAME|exact(proj1 SEPARATE)|exact FIRST].
  - eapply namespace_partial_preserves_load;[exact FRAME|exact OBJECT_TLS|exact LOAD].
Qed.

Lemma prepared_check_duplicate_frame le memory first second failure reply:
  child_scope_registers scope le ->le!_failure=Some(Vint failure) ->0<=Int.signed failure ->
  child_storage_separate cell objects ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 80(child_closed_log scope first second failure reply)
    (State f_create_entry_child(child_tail 3(fn_body f_create_entry_child))k(child_env pair)le memory).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE STORAGE FIRST LOAD.
  eapply namespace_trace_weaken with(n:=77%nat);[|lia].
  eapply namespace_trace_store_path with(count:=3%nat)(remaining:=74%nat).
  - eapply child_duplicate_nonnegative_source;eassumption.
  - eapply prepared_mask_tail_frame;eassumption.
Qed.

Lemma prepared_close_original_frame le memory first second failure:
  child_scope_registers scope le ->le!_failure=Some(Vint failure) ->0<=Int.signed failure ->
  child_storage_separate cell objects ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory pair 4=Some(Vint second) ->
  Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 88(child_duplicate_log scope first second failure)
    (State f_create_entry_child(child_tail 2(fn_body f_create_entry_child))k(child_env pair)le memory).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE STORAGE FIRST SECOND LOAD.
  eapply namespace_trace_store_path with(count:=5%nat)(remaining:=83%nat);[apply child_close_original_source;exact SECOND|].
  eapply namespace_trace_close;[apply entry_errno_ready_tls;exact(proj1 STORAGE)|].
  intros reply after CLOSE.
  assert(READY:entry_errno_ready cell after)by(eapply namespace_errno_ready_close;[exact(proj1 STORAGE)|exact CLOSE]).
  eapply namespace_trace_store_path with(count:=2%nat)(remaining:=80%nat);[apply child_close_original_return_source|].
  eapply prepared_check_duplicate_frame;try eassumption.
  - unfold child_original_close_env;child_scope_registers.
  - unfold child_original_close_env;WriteAll.lookup.
  - eapply child_storage_close;eassumption.
  - eapply namespace_close_preserves_load;[exact CLOSE|exact(proj1 SEPARATE)|exact FIRST].
  - eapply namespace_close_preserves_load;[exact CLOSE|exact OBJECT_TLS|exact LOAD].
Qed.

Lemma prepared_duplicate_return_frame le memory first second failure:
  child_scope_registers scope le ->child_storage_separate cell objects ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory pair 4=Some(Vint second) ->
  Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 92
    (child_pair_log scope first second++[namespace_duplicated second(Int.repr 60)failure])
    (Returnstate(Vint failure)(child_duplicate_cont pair le second k)memory).
Proof.
  intros REGISTERS SEPARATE STORAGE FIRST SECOND LOAD;destruct(zlt(Int.signed failure)0)as[NEGATIVE|NONNEGATIVE].
  - apply namespace_trace_stop;apply prepared_bad_last;[|exact I|cbn[prepared_setup_success];lia].
    eapply prepared_nonfork_log;[exact HISTORY|apply child_pair_before_fork].
  - eapply namespace_trace_store_path with(count:=4%nat)(remaining:=88%nat);[apply child_duplicate_return_source|].
    eapply prepared_close_original_frame;try eassumption;try lia.
    + unfold child_duplicate_return_env,child_duplicate_call_env;child_scope_registers.
    + unfold child_duplicate_return_env;WriteAll.lookup.
Qed.

Lemma prepared_duplicate_tail_frame le memory first second:
  child_scope_registers scope le ->child_storage_separate cell objects ->child_storage cell objects memory ->
  Mem.load Mint32 memory pair 0=Some(Vint first) ->Mem.load Mint32 memory pair 4=Some(Vint second) ->
  Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 99(child_pair_log scope first second)
    (State f_create_entry_child(child_tail 1(fn_body f_create_entry_child))k(child_env pair)le memory).
Proof.
  intros REGISTERS SEPARATE STORAGE FIRST SECOND LOAD.
  eapply namespace_trace_store_path with(count:=6%nat)(remaining:=93%nat);[apply child_duplicate_source;exact SECOND|].
  eapply namespace_trace_duplicate;[exact(proj1 STORAGE)|].
  intros failure after FRAME READY;eapply prepared_duplicate_return_frame;try eassumption.
  - eapply child_storage_partial;eassumption.
  - eapply namespace_partial_preserves_load;[exact FRAME|exact(proj1 SEPARATE)|exact FIRST].
  - eapply namespace_partial_preserves_load;[exact FRAME|exact(proj1 SEPARATE)|exact SECOND].
  - eapply namespace_partial_preserves_load;[exact FRAME|exact OBJECT_TLS|exact LOAD].
Qed.

Lemma prepared_pair_return_frame le memory returned first second:
  child_scope_registers scope le ->child_storage_separate cell objects ->child_storage cell objects memory ->
  (returned=Int.zero ->Mem.load Mint32 memory pair 0=Some(Vint first) /\Mem.load Mint32 memory pair 4=Some(Vint second)) ->
  Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 105
    (scope_history scope++[namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero pair Ptrofs.zero returned first second])
    (Returnstate(Vint returned)(child_socket_cont pair le k)memory).
Proof.
  intros REGISTERS SEPARATE STORAGE CELLS LOAD;destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;destruct(CELLS(Logic.eq_refl _))as[FIRST SECOND].
    eapply namespace_trace_weaken with(n:=103%nat);[|lia].
    eapply namespace_trace_store_path with(count:=4%nat)(remaining:=99%nat);[apply child_socket_success_source|].
    eapply prepared_duplicate_tail_frame;try eassumption;child_scope_registers.
  - apply namespace_trace_stop;apply prepared_bad_last;[rewrite HISTORY;constructor|exact I|exact NONZERO].
Qed.

Theorem prepared_child_body_cgroup_frame le memory:
  child_scope_registers scope le ->child_storage_separate cell objects ->child_storage cell objects memory ->
  Mem.load Mint32 memory object 0=Some value ->
  namespace_trace_region namespace_ge cell result 109(scope_history scope)
    (State f_create_entry_child(fn_body f_create_entry_child)k(child_env pair)le memory).
Proof.
  intros REGISTERS SEPARATE STORAGE LOAD.
  eapply namespace_trace_store_path with(count:=3%nat)(remaining:=106%nat);[apply child_socket_source|].
  eapply namespace_trace_pair;[eapply child_pair_is_writable;exact STORAGE|exact(proj1 STORAGE)|].
  intros returned first second after EFFECT READY;eapply prepared_pair_return_frame;try eassumption.
  - eapply child_storage_permissions;[exact STORAGE|exact READY|eapply namespace_pair_permissions;exact EFFECT].
  - intros ZERO;subst returned.
    exact(namespace_pair_returned_cells cell memory after pair Ptrofs.zero first second(proj1 SEPARATE)EFFECT).
  - eapply prepared_pair_frame;[exact OBJECT_TLS|exact OBJECT_PAIR|exact EFFECT|exact LOAD].
Qed.
End COMMON_BODY.

Theorem prepared_child_call_cgroup_frame request before object value:
  request_history request=[] ->object<>tls_block(request_cell request) ->object<>request_peer request ->
  Mem.load Mint32 before object 0=Some value ->
  handoff_borrowed_input(request_cell request)before(request_borrowed request) ->
  Mem.range_perm before(request_peer request)0 4 Cur Freeable ->
  Mem.range_perm before(request_pid request)0 4 Cur Freeable ->
  request_peer request<>request_pid request ->request_peer request<>tls_block(request_cell request) ->
  request_pid request<>tls_block(request_cell request) ->
  exists pair,namespace_trace_region namespace_ge(request_cell request)
    (prepared_cgroup_result(request_scope request pair)object value)110(request_history request)
    (Callstate(Internal f_create_entry_child)(child_values(request_arguments request))(request_continuation request)before).
Proof.
  intros HISTORY OBJECT_TLS OBJECT_PEER LOAD INPUT PEER PID DISTINCT PEER_TLS PID_TLS.
  destruct(child_entry_allocates before(request_arguments request)(request_continuation request))
    as[pair[after[ENTRY[ALLOC[OLD[FRESH PAIR]]]]]].
  assert(PEER_VALID:Mem.valid_block before(request_peer request)).
  { eapply Mem.perm_valid_block with(ofs:=0);apply PEER;lia. }
  assert(PID_VALID:Mem.valid_block before(request_pid request)).
  { eapply Mem.perm_valid_block with(ofs:=0);apply PID;lia. }
  assert(TLS_VALID:Mem.valid_block before(tls_block(request_cell request))).
  { destruct(handoff_borrowed_errno _ _ _ INPUT)as[error[LOW[HIGH[ACCESS LOAD_ERRNO]]]].
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(OBJECT_VALID:Mem.valid_block before object).
  { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
      [eapply Mem.load_valid_access;exact LOAD|constructor]. }
  assert(PAIR_TLS:pair<>tls_block(request_cell request))by(intro SAME;subst pair;contradiction).
  assert(PEER_PAIR:request_peer request<>pair)by(intro SAME;subst pair;contradiction).
  assert(PID_PAIR:request_pid request<>pair)by(intro SAME;subst pair;contradiction).
  assert(OBJECT_PAIR:object<>pair)by(intro SAME;subst pair;contradiction).
  assert(INPUT_AFTER:handoff_borrowed_input(request_cell request)after(request_borrowed request)).
  { eapply namespace_allocation_preserves_borrows;[exact INPUT|exact ALLOC]. }
  exists pair;eapply namespace_trace_source_prepend;[exact ENTRY|].
  eapply(prepared_child_body_cgroup_frame(request_scope request pair)object value
    HISTORY OBJECT_TLS OBJECT_PAIR OBJECT_PEER).
  - unfold child_scope_registers,request_scope,child_parameters,request_arguments;cbn;repeat split;WriteAll.lookup.
  - unfold child_storage_separate,request_scope;cbn;repeat split;assumption.
  - unfold child_storage,request_scope;cbn;split;[exact(handoff_borrowed_errno _ _ _ INPUT_AFTER)|].
    split;[exact PAIR|]. split;intros position RANGE;eapply local_allocations_perms;
      [exact ALLOC|apply PEER;exact RANGE|exact ALLOC|apply PID;exact RANGE].
  - eapply child_allocation_preserves_load;[exact ALLOC|exact LOAD].
Qed.

Theorem prepared_root_cgroup_frame before prepared cell borrowed input output errors le object value:
  Mem.valid_block before(tls_block cell) ->Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  Mem.valid_block before object ->object<>tls_block cell ->Mem.load Mint32 prepared object 0=Some value ->
  handoff_borrowed_input cell prepared borrowed ->
  (forall target position kind permission,Mem.perm(namespace_initial_memory before)target position kind permission ->
    Mem.perm prepared target position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  exists peer pid pair,
    let scope:={|scope_cell:=cell;scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
      scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
      scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|} in
    namespace_trace_region namespace_ge cell(prepared_cgroup_result scope object value)114[]
      (State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared).
Proof.
  intros TLS BLOCKS OBJECT_VALID OBJECT_TLS LOAD INPUT PERMISSIONS ERROR IN OUT ERR.
  destruct(namespace_entry_owns_child_outputs before cell borrowed TLS BLOCKS)
    as[peer[pid[PEER[PID[PEER_OWNED[PID_OWNED[DISTINCT[PEER_TLS[PID_TLS[PEER_PRIVATE PID_PRIVATE]]]]]]]]]].
  assert(OBJECT_PEER:object<>peer).
  { destruct(namespace_owned_local_from_entry before _pipefd(tarray tint 2)ltac:(cbn;auto 12))
      as[actual[PRESENT[FRESH OWNED]]].
    rewrite prepared_canonical_env_form in PRESENT.
    rewrite PEER in PRESENT;inversion PRESENT;subst actual.
    intro SAME;subst object;apply FRESH;exact OBJECT_VALID. }
  set(request:={|request_cell:=cell;request_borrowed:=borrowed;request_input:=input;request_output:=output;
    request_errors:=errors;request_peer:=peer;request_pid:=pid;
    request_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;request_history:=[]|}).
  destruct(prepared_child_call_cgroup_frame request prepared object value
    (Logic.eq_refl _)OBJECT_TLS OBJECT_PEER LOAD INPUT
    ltac:(intros position RANGE;apply PERMISSIONS;apply PEER_OWNED;lia)
    ltac:(intros position RANGE;apply PERMISSIONS;apply PID_OWNED;exact RANGE)
    DISTINCT PEER_TLS PID_TLS)as[pair CERT].
  exists peer,pid,pair;eapply namespace_trace_store_path with(count:=4%nat)(remaining:=110%nat).
  - eapply namespace_create_call_source;eauto.
  - exact CERT.
Qed.

Lemma prepared_cgroup_region_at_fork scope object value n log before continuation returned after:
  namespace_trace_region namespace_ge(scope_cell scope)(prepared_cgroup_result scope object value)n log
    (Callstate namespace_fork_definition[]continuation before) ->
  namespace_step namespace_ge(scope_cell scope)
    (live(Callstate namespace_fork_definition[]continuation before))(namespace_forked returned)
    (live(Returnstate(Vint returned)continuation after)) ->
  prepared_cgroup_result scope object value log(Callstate namespace_fork_definition[]continuation before).
Proof.
  intros CERT STEP;inversion CERT as[count history state RESULT|count history state PROGRESS CASES];subst.
  - exact RESULT.
  - destruct(CASES _ _ STEP)as[[WAIT TARGET]|[[dead[TARGET NOIMAGE]]|[next[TARGET[ADV[NOIMAGE TAIL]]]]]];
      try discriminate.
    inversion TARGET;subst next.
    destruct(namespace_trace_actual _ _ _ _ _ _ TAIL)as[events[endpoint[RUN[COST[IMAGES RESULT]]]]].
    destruct RESULT as[FREE REST];rewrite Forall_forall in FREE.
    specialize(FREE(namespace_forked returned));exfalso;apply FREE.
    unfold namespace_advance;cbn[namespace_fd_event].
    apply in_or_app;left;apply in_or_app;right;cbn;auto.
Qed.

Lemma prepared_cgroup_result_at_fork scope object value log continuation before:
  Forall prepared_setup_success log ->
  prepared_cgroup_result scope object value log(Callstate namespace_fork_definition[]continuation before) ->
  Mem.load Mint32 before object 0=Some value.
Proof.
  intros SUCCESS[FREE[[event[MEMBER BAD]]|[temps[memory[SAME LOAD]]]]].
  - rewrite Forall_forall in SUCCESS;exfalso;apply BAD;apply SUCCESS;exact MEMBER.
  - inversion SAME;subst;exact LOAD.
Qed.

Lemma prepared_signal_log_success scope first second failure reply:
  scope_history scope=[] ->0<=Int.signed failure ->
  Forall prepared_setup_success(child_signal_log scope first second failure reply).
Proof.
  intros HISTORY NONNEGATIVE;unfold child_signal_log,child_mask_log,child_closed_log,child_duplicate_log,child_pair_log.
  rewrite HISTORY;cbn;repeat constructor;exact NONNEGATIVE.
Qed.

From EntryProcess Require Import ProcessJournal.
From EntryNamespace Require Import NamespaceSourceFork.

Theorem actual_prepared_common_cgroup_load(run:CallerSourceRun)returned(fork:ActualSourceFork run returned)
    before prepared borrowed input output errors le object value:
  source_before run=live(State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared) ->
  Mem.valid_block before(tls_block(source_cell run)) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  Mem.valid_block before object ->object<>tls_block(source_cell run) ->Mem.load Mint32 prepared object 0=Some value ->
  handoff_borrowed_input(source_cell run)prepared borrowed ->
  (forall target position kind permission,Mem.perm(namespace_initial_memory before)target position kind permission ->
    Mem.perm prepared target position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  Forall prepared_setup_success(namespace_fd_events(source_fork_common _ _ fork)) ->
  Mem.load Mint32(source_fork_before _ _ fork)object 0=Some value.
Proof.
  intros START TLS BLOCKS OBJECT_VALID OBJECT_TLS LOAD INPUT PERMISSIONS ERROR IN OUT ERR SUCCESS.
  destruct(prepared_root_cgroup_frame before prepared(source_cell run)borrowed input output errors le object value
    TLS BLOCKS OBJECT_VALID OBJECT_TLS LOAD INPUT PERMISSIONS ERROR IN OUT ERR)as[peer[pid[pair CERT]]].
  pose(scope:={|scope_cell:=source_cell run;
    scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
    scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
    scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|}).
  change(namespace_trace_region namespace_ge(source_cell run)(prepared_cgroup_result scope object value)114[]
    (State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared))in CERT.
  pose proof(source_fork_prefix _ _ fork)as PREFIX;rewrite START in PREFIX;rewrite <-prepared_fork_environment in PREFIX.
  pose proof(source_fork_operation _ _ fork)as FORK;rewrite <-prepared_fork_environment in FORK.
  destruct(namespace_trace_execution_split _ _ _ _ _ _ CERT _ _ PREFIX)
    as[[COST[IMAGES RESIDUAL]]|[prefix[endpoint[rest[EVENTS[COST[IMAGES[PRE[RESULT SUFFIX]]]]]]]]].
  - destruct(RESIDUAL _(Logic.eq_refl _))as[remaining REGION];cbn[app]in REGION.
    eapply prepared_cgroup_result_at_fork with(scope:=scope);[exact SUCCESS|].
    eapply prepared_cgroup_region_at_fork with(scope:=scope);[exact REGION|exact FORK].
  - cbn[app]in RESULT;destruct RESULT as[FREE[[event[MEMBER BAD]]|[temps[memory[SAME KEPT]]]]].
    + rewrite EVENTS in SUCCESS;unfold namespace_fd_events in SUCCESS;rewrite filter_app in SUCCESS;apply Forall_app in SUCCESS as[GOOD REST].
      rewrite Forall_forall in GOOD;exfalso;apply BAD;apply GOOD;exact MEMBER.
    + subst endpoint.
      destruct(actual_common_fork_only_waits(source_cell run)pair temps(namespace_initial_env before)le
        memory rest(source_fork_continuation _ _ fork)(source_fork_before _ _ fork)
        (prepared_canonical_env_global before)SUFFIX)as[CONT[MEMORY EMPTY]].
      rewrite MEMORY;exact KEPT.
Qed.

Theorem actual_prepared_parent_cgroup_load(run:CallerSourceRun)returned(fork:ActualSourceFork run returned)
    before prepared borrowed input output errors le object value:
  source_before run=live(State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared) ->
  Mem.valid_block before(tls_block(source_cell run)) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  Mem.valid_block before object ->object<>tls_block(source_cell run) ->Mem.load Mint32 prepared object 0=Some value ->
  handoff_borrowed_input(source_cell run)prepared borrowed ->
  (forall target position kind permission,Mem.perm(namespace_initial_memory before)target position kind permission ->
    Mem.perm prepared target position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  Forall prepared_setup_success(namespace_fd_events(source_fork_common _ _ fork)) ->
  Mem.load Mint32(source_fork_parent _ _ fork)object 0=Some value.
Proof.
  intros START TLS BLOCKS OBJECT_VALID OBJECT_TLS LOAD INPUT PERMISSIONS ERROR IN OUT ERR SUCCESS.
  pose proof(actual_prepared_common_cgroup_load run returned fork before prepared borrowed input output errors le object value
    START TLS BLOCKS OBJECT_VALID OBJECT_TLS LOAD INPUT PERMISSIONS ERROR IN OUT ERR SUCCESS)as COMMON.
  pose proof(source_fork_operation _ _ fork)as FORK;rewrite <-prepared_fork_environment in FORK.
  destruct(namespace_fork_cases _ _ _ _ _ _ FORK)
    as[[actual[after[PARTIAL[READY[EVENT TARGET]]]]]|[[EVENT TARGET]|[[after[PARTIAL[EVENT TARGET]]]|[EVENT TARGET]]]];
    try discriminate.
  inversion TARGET;subst after.
  eapply namespace_partial_preserves_load;[exact PARTIAL|exact OBJECT_TLS|exact COMMON].
Qed.
