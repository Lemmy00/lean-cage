(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: One actual recorded fork supplies the checked parent grant and its original arguments. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import IO Machine ArgumentsImport.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput NativeHandoffWire NativeValues.
From EntryProcess Require Import ProcessMachine ProcessJournal ProcessReleaseSafety.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceStructure NamespacePaths NamespaceMemory
  NamespaceChildResult NamespaceForkPrefix NamespaceFork NamespaceForkInputs NamespaceSourceFork NamespaceGrantInputs
  NamespaceSocket NamespaceCaller NamespaceParentEntry NamespaceParentSafety NamespaceRecordedParent NamespaceTLS NamespaceTraceRegion.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Theorem actual_same_fork_source_write_authorized scope first second failure reply world before_world snapshot
    run(fork:ActualSourceFork run(task_pid(fork_child snapshot)))child_memory
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    cgroup_binding report_binding ordinal event io:
  scope_history scope=[] ->source_cell run=scope_cell scope ->
  ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
    (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)) ->
  namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply ->
  NamespaceWorldTrace.namespace_kernel_steps before_world(source_fork_common _ _ fork)world ->
  fork_matches world snapshot ->
  NativeForkCopy(scope_cell scope)(source_fork_before _ _ fork)(source_fork_parent _ _ fork)child_memory ->
  Lean.eq(argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight(scope_borrowed scope))))
    (argument_bytes(map Byte.repr[114;117;110])) ->
  namespace_table before_world(prepared_cgroup_fd input)=Some cgroup_binding ->
  namespace_table before_world(prepared_report_fd input)=Some report_binding ->
  (S(length(source_fork_common _ _ fork))<=ordinal)%nat ->
  nth_error(source_events run)ordinal=Some event ->namespace_socket_io event=Some io ->
  operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=first ->
  exists finish_prefix setup_prefix ready grant_prefix release_prefix resume,
    Forall(fun event=>namespace_parent_prelude_event event=true)(finish_prefix++setup_prefix) /\
    Forall(namespace_parent_closes_from[failure;scope_input scope;scope_output scope;scope_errors scope;prepared_parent_fd input])
      (finish_prefix++setup_prefix) /\
    firstn(ordinal-S(length(source_fork_common _ _ fork)))(source_fork_body _ _ fork)=
      finish_prefix++setup_prefix++grant_prefix++release_prefix /\
    namespace_steps ProcessGlobalCalls.caller_ge(source_cell run)
      (live(Returnstate(Vint(task_pid(fork_child snapshot)))(source_fork_continuation _ _ fork)(source_fork_parent _ _ fork)))
      (finish_prefix++setup_prefix)
      (live(State f_namespace_init(namespace_tail 20)Kstop(prepared_parent_env input)
        (namespace_parent_setup_env(prepared_parent_temps input)(task_pid(fork_child snapshot)))ready)) /\
    namespace_authorized_parent(scope_cell scope)ready(task_pid(fork_child snapshot))first(prepared_cgroup_fd input)
      (prepared_status_cell input)(prepared_result_temporary input)(prepared_admission_cell input)
      (prepared_report_fd input)(prepared_sequence input)grant_prefix /\
    nth_error(source_events run)resume=Some(namespace_process(release_resume_event(task_pid(fork_child snapshot)))) /\
    (S(length(source_fork_common _ _ fork))+length finish_prefix+length setup_prefix+length grant_prefix<=resume)%nat /\
    (S(length(source_fork_common _ _ fork))<=resume<ordinal)%nat /\
    requested(source_socket_request io)=1 /\source_socket_bytes io=[Byte.repr 165].
Proof.
  intros HISTORY CELL FRONTIER LOG KERNEL MATCH COPY MODE CGROUP_BINDING REPORT_BINDING
    LOWER SELECTED SOCKET WRITING DESCRIPTOR.
  rewrite LOG in FRONTIER.
  destruct(actual_common_fork_continuation _ _ _ _ _ _ _ FRONTIER)as[child_temps CONTINUATION].
  rewrite CONTINUATION in FRONTIER.
  destruct(same_fork_parent_borrowed_inputs _ _ _ _ _ _ _ _ _ FRONTIER COPY)
    as[BORROWED[PEER[REGISTERS[FAILURE[SEPARATE PRIVATE]]]]].
  destruct REGISTERS as[IN[OUT[ERR[PEER_POINTER CHILD_POINTER]]]].
  destruct SEPARATE as[PAIR_TLS[PIPE_TLS[CHILD_TLS[PIPE_PAIR[CHILD_PAIR PIPE_CHILD]]]]].
  destruct PRIVATE as[PAIR_PRIVATE[PIPE_PRIVATE CHILD_PRIVATE]].
  assert(PREFLIGHT_MEMBER:In(namespace_symbol _preflight)(handoff_borrowed_blocks(scope_borrowed scope))).
  { change(In(handoff_symbol _preflight)(handoff_borrowed_blocks(scope_borrowed scope))).
    apply handoff_borrowed_global_member;cbn;auto. }
  assert(PREFLIGHT_TLS:namespace_symbol _preflight<>tls_block(scope_cell scope)).
  { pose proof(handoff_borrowed_tls_separate _ _ _ BORROWED)as TLS.
    rewrite Forall_forall in TLS;apply TLS;exact PREFLIGHT_MEMBER. }
  assert(PREFLIGHT_CHILD:namespace_symbol _preflight<>storage_pid(scope_storage scope)).
  { intro SAME;apply CHILD_PRIVATE;rewrite <-SAME;exact PREFLIGHT_MEMBER. }
  assert(PREFLIGHT_PAIR:namespace_symbol _preflight<>storage_pair(scope_storage scope)).
  { intro SAME;apply PAIR_PRIVATE;rewrite <-SAME;exact PREFLIGHT_MEMBER. }
  pose proof(strict_same_fork_normal_parent_preflight _ _ _ _ _ _ _ _ _ FRONTIER COPY MODE)as CHECK.
  change(Mem.load Mint32(source_fork_parent _ _ fork)(namespace_symbol _preflight)0=Some(Vint Int.zero))in CHECK.
  pose proof(prepared_parent_registers input)as[INPUT[OUTPUT[ERRORS[PARENT[REPORT SEQUENCE]]]]].
  pose proof(prepared_parent_cells input)as[CHILD[PIPE[STATUS[CGROUP[PREFLIGHT[TEMPORARY ADMISSION]]]]]].
  pose proof(prepared_status_separation input)as[STATUS_CHILD[STATUS_PIPE[STATUS_CGROUP STATUS_CHECK]]].
  pose proof(prepared_cgroup_local_separation input)as[CGROUP_CHILD CGROUP_PAIR].
  pose proof(prepared_parent_continuation input)as CALLER.
  assert(TLS:Mem.valid_block(source_fork_parent _ _ fork)(tls_block(scope_cell scope))).
  { apply namespace_errno_ready_valid;exact(handoff_borrowed_errno _ _ _ BORROWED). }
  assert(POSITIVE:(0<=Int.signed(task_pid(fork_child snapshot))))by(pose proof(fork_child_positive snapshot);lia).
  assert(NONZERO:task_pid(fork_child snapshot)<>Int.zero).
  { intro SAME;pose proof(fork_child_positive snapshot)as LIVE;rewrite SAME,Int.signed_zero in LIVE;lia. }
  destruct(NamespaceForkWorld.source_common_fork_world _ _ _ _ _ _ _ _ _ _ HISTORY
    ltac:(rewrite LOG;exact FRONTIER)LOG KERNEL)
    as[channel[inherited[WORLD[DEFAULT[MASK[D0[D1[MINIMUM[FIRST[CHILD_ENDPOINT[CLOEXEC[AMBIENT OLD]]]]]]]]]]]].
  assert(TABLE:namespace_table world=inherited).
  { rewrite WORLD;unfold NamespaceWorldTrace.child_fork_world,namespace_default_action;rewrite Int.eq_true;reflexivity. }
  assert(CG_OTHER:prepared_cgroup_fd input<>first).
  { eapply prepared_old_descriptor_differs_peer;[exact HISTORY| |exact LOG|exact KERNEL| |exact CGROUP_BINDING].
    - rewrite LOG;exact FRONTIER.
    - rewrite TABLE;exact FIRST. }
  assert(REPORT_OTHER:prepared_report_fd input<>first).
  { eapply prepared_old_descriptor_differs_peer;[exact HISTORY| |exact LOG|exact KERNEL| |exact REPORT_BINDING].
    - rewrite LOG;exact FRONTIER.
    - rewrite TABLE;exact FIRST. }
  pose proof(source_fork_suffix _ _ fork)as SUFFIX.
  change(namespace_steps namespace_ge(source_cell run)
    (live(Returnstate(Vint(task_pid(fork_child snapshot)))(source_fork_continuation _ _ fork)(source_fork_parent _ _ fork)))
    (source_fork_body _ _ fork)(source_after run))in SUFFIX.
  rewrite CELL,CONTINUATION,CALLER in SUFFIX.
  destruct(actual_recorded_positive_fork_write(scope_cell scope)(storage_pair(scope_storage scope))child_temps failure
    (prepared_parent_env input)(prepared_parent_temps input)(source_fork_parent _ _ fork)
    (scope_input scope)(scope_output scope)(scope_errors scope)(prepared_parent_fd input)
    (storage_pid(scope_storage scope))(storage_peer(scope_storage scope))(prepared_status_cell input)
    (task_pid(fork_child snapshot))first(prepared_cgroup_fd input)(prepared_result_temporary input)(prepared_admission_cell input)
    (prepared_report_fd input)(prepared_sequence input)run(source_fork_common _ _ fork)(source_fork_body _ _ fork)ordinal event io
    (prepared_parent_global input)CHILD_POINTER FAILURE NONZERO INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE
    CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION POSITIVE PEER(prepared_parent_cgroup_load input)CHECK
    CHILD_TLS PIPE_TLS(prepared_cgroup_tls input)PREFLIGHT_TLS STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK
    CHILD_PAIR PIPE_CHILD PIPE_PAIR CGROUP_CHILD CGROUP_PAIR PREFLIGHT_CHILD PREFLIGHT_PAIR TLS CG_OTHER REPORT_OTHER
    CELL(source_fork_events _ _ fork)SUFFIX LOWER SELECTED SOCKET WRITING DESCRIPTOR)
    as[finish_prefix[setup_prefix[ready[grant_prefix[release_prefix[resume
      [QUIET[CLOSED[ORDER[SETUP[AUTHORIZED[RESUMED[AFTER[BEFORE[COUNT BYTES]]]]]]]]]]]]]]].
  exists finish_prefix,setup_prefix,ready,grant_prefix,release_prefix,resume.
  split;[exact QUIET|]. split;[exact CLOSED|]. split;[exact ORDER|]. split.
  - rewrite CELL,CONTINUATION,CALLER;exact SETUP.
  - repeat first[assumption|split].
Qed.
