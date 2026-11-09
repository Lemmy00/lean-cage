(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The real prepared source prefix supplies the scope consumed by admission. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
From LeanImport Require Import Lean.
Require Import IO Machine ArgumentsImport.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput NativeHandoffWire NativeValues.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessSourceRecording ProcessSourceTables
  ProcessCapabilityRecording ProcessCapabilityBirth.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceMachine NamespaceMemory NamespacePaths
  NamespaceCaller NamespaceStructure NamespaceAllocation NamespacePrepared NamespacePreparedFork NamespaceChildResult NamespaceForkPrefix
  NamespaceFork NamespaceSourceFork NamespaceGrantInputs NamespaceQueue NamespaceChannel NamespacePhysical
  NamespaceGuestFlags NamespaceAdmissionGuarantee NamespacePreparedCgroupFrame NamespaceForkInputs NamespaceTraceRegion.
From EntryReporting Require Import ResultLayout.
Import ListNotations.
Local Close Scope lean_scope.

(* §AR-entry.caller: Local storage and separation follow from the real allocation. *)
Theorem namespace_actual_parent_storage before prepared parent_memory scope first le parentfd report cgroup sequence:
  scope_continuation scope=namespace_creation_cont(namespace_initial_env before)le Kstop ->
  (namespace_initial_env before)!_pipefd=Some(storage_peer(scope_storage scope),Ctypesdefs.tarray Ctypesdefs.tint 2) ->
  (namespace_initial_env before)!_child=Some(storage_pid(scope_storage scope),Ctypesdefs.tint) ->
  ~Mem.valid_block prepared(storage_pair(scope_storage scope)) ->
  Mem.valid_block before(tls_block(scope_cell scope)) ->
  Mem.valid_block before(namespace_symbol _admission_cgroup) ->
  Mem.valid_block before(namespace_symbol _preflight) ->
  Mem.valid_block prepared(namespace_symbol _admission_cgroup) ->
  namespace_symbol _admission_cgroup<>tls_block(scope_cell scope) ->
  Mem.load Mint32 parent_memory(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  le!_input=Some(Vint(scope_input scope)) ->le!_output=Some(Vint(scope_output scope)) ->
  le!_errors=Some(Vint(scope_errors scope)) ->le!_parentfd=Some(Vint parentfd) ->
  le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  cgroup<>scope_input scope ->cgroup<>scope_output scope ->cgroup<>scope_errors scope ->cgroup<>parentfd ->
  exists parent:ParentPreparedInput scope first parent_memory,
    prepared_parent_env parent=namespace_initial_env before /\prepared_parent_temps parent=le /\
    prepared_parent_fd parent=parentfd /\prepared_report_fd parent=report /\
    prepared_cgroup_fd parent=cgroup /\prepared_sequence parent=sequence.
Proof.
  intros CONT PIPE CHILD PAIR_FRESH TLS CGROUP PREFLIGHT CG_PREPARED CG_TLS CG_LOAD IN OUT ERR PARENT REPORT SEQUENCE
    CG_IN CG_OUT CG_ERR CG_PARENT.
  destruct(namespace_owned_local_from_entry before _status Ctypesdefs.tint ltac:(cbn;auto 12))
    as[status[STATUS[STATUS_FRESH STATUS_OWNED]]].
  destruct(namespace_owned_local_from_entry before __res__6 EntryReporting.ResultLayout.result_type ltac:(cbn;auto 20))
    as[temporary[TEMPORARY[TEMPORARY_FRESH TEMPORARY_OWNED]]].
  destruct(namespace_owned_local_from_entry before _admission EntryReporting.ResultLayout.result_type ltac:(cbn;auto 12))
    as[admission[ADMISSION[ADMISSION_FRESH ADMISSION_OWNED]]].
  rewrite prepared_canonical_env_form in STATUS,TEMPORARY,ADMISSION.
  destruct(namespace_allocate_variables_source(fn_vars f_namespace_init)empty_env before)as[ALLOC OBJECTS].
  rewrite prepared_canonical_env_form,prepared_canonical_memory_form in ALLOC.
  pose proof(namespace_function_entry before _ _ Int.zero Int.zero Int.zero Int.zero Int.zero ALLOC)as ENTRY.
  destruct(actual_namespace_parent_local_separation before _ _ _ _ (scope_cell scope)
    (storage_pid(scope_storage scope))(storage_peer(scope_storage scope))status
    ENTRY TLS CGROUP PREFLIGHT CHILD PIPE STATUS)as[CHILD_TLS[PIPE_TLS[STATUS_TLS[STATUS_CHILD[STATUS_PIPE[STATUS_CG STATUS_PF]]]]]].
  assert(FRESH:namespace_old_env_fresh before(namespace_initial_env before)).
  { eapply namespace_actual_allocation_fresh;[exact ALLOC|intros object VALID;exact VALID|].
    intros id object ty LOOKUP;rewrite PTree.gempty in LOOKUP;discriminate. }
  destruct(namespace_entry_callees_are_global before)as[C0[C1[C2[CGLOBAL[C4[C5[C6[C7 PGLOBAL]]]]]]]].
  assert(CG_CHILD:namespace_symbol _admission_cgroup<>storage_pid(scope_storage scope)).
  { intro SAME;apply(FRESH _ _ _ CHILD);rewrite <-SAME;exact CGROUP. }
  assert(CG_PAIR:namespace_symbol _admission_cgroup<>storage_pair(scope_storage scope)).
  { intro SAME;apply PAIR_FRESH;rewrite <-SAME;exact CG_PREPARED. }
  assert(CELLS:(namespace_initial_env before)!_child=Some(storage_pid(scope_storage scope),Ctypesdefs.tint) /\
    (namespace_initial_env before)!_pipefd=Some(storage_peer(scope_storage scope),Ctypesdefs.tarray Ctypesdefs.tint 2) /\
    (namespace_initial_env before)!_status=Some(status,Ctypesdefs.tint) /\
    (namespace_initial_env before)!_admission_cgroup=None /\(namespace_initial_env before)!_preflight=None /\
    (namespace_initial_env before)!__res__6=Some(temporary,EntryReporting.ResultLayout.result_type) /\
    (namespace_initial_env before)!_admission=Some(admission,EntryReporting.ResultLayout.result_type))
    by(repeat split;assumption).
  assert(REGISTERS:le!_input=Some(Vint(scope_input scope)) /\le!_output=Some(Vint(scope_output scope)) /\
    le!_errors=Some(Vint(scope_errors scope)) /\le!_parentfd=Some(Vint parentfd) /\le!_report=Some(Vint report) /\
    le!_sequence=Some(Vlong sequence))by(repeat split;assumption).
  pose(parent:={|
    prepared_parent_env:=namespace_initial_env before;prepared_parent_temps:=le;
    prepared_parent_fd:=parentfd;prepared_report_fd:=report;prepared_cgroup_fd:=cgroup;prepared_sequence:=sequence;
    prepared_status_cell:=status;prepared_result_temporary:=temporary;prepared_admission_cell:=admission;
    prepared_parent_continuation:=CONT;prepared_parent_global:=prepared_canonical_env_global before;
    prepared_parent_registers:=REGISTERS;prepared_parent_cells:=CELLS;prepared_parent_cgroup_load:=CG_LOAD;
    prepared_cgroup_tls:=CG_TLS;prepared_cgroup_sources:=conj CG_IN(conj CG_OUT(conj CG_ERR CG_PARENT));
    prepared_status_separation:=conj STATUS_CHILD(conj STATUS_PIPE(conj STATUS_CG STATUS_PF));
    prepared_status_tls:=STATUS_TLS;prepared_cgroup_local_separation:=conj CG_CHILD CG_PAIR|}
    :ParentPreparedInput scope first parent_memory).
  exists parent;repeat split;reflexivity.
Qed.

(* The result chooses the actual fresh local scope before consuming raw parent
   preparation inputs. No caller provides a successful local frontier or FD log. *)
Theorem actual_prepared_recorded_fork_admission
    run snapshot(fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    before prepared borrowed input output errors le:
  source_before run=live(State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared) ->
  Mem.valid_block before(tls_block(source_cell run)) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  handoff_borrowed_input(source_cell run)prepared borrowed ->
  (forall object position kind permission,Mem.perm(namespace_initial_memory before)object position kind permission ->
    Mem.perm prepared object position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->
  le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  exists(scope:ChildScope)(first second failure:int)(reply:ProcessEffects.close_reply),
    scope_cell scope=source_cell run /\scope_borrowed scope=borrowed /\
    scope_input scope=input /\scope_output scope=output /\scope_errors scope=errors /\
    scope_history scope=[] /\scope_continuation scope=
      namespace_creation_cont(namespace_initial_env before)le Kstop /\
    (namespace_initial_env before)!_pipefd=Some(storage_peer(scope_storage scope),Ctypesdefs.tarray Ctypesdefs.tint 2) /\
    (namespace_initial_env before)!_child=Some(storage_pid(scope_storage scope),Ctypesdefs.tint) /\
    ~Mem.valid_block prepared(storage_pair(scope_storage scope)) /\
    forall operation groups runs native metadata external can_acquire pair_primitive fork_primitive
      (platform:NamespaceQueueContract)cursor worlds ticks final final_worlds world before_world before_queues fork_queues
      owner child parent_program child_program child_memory
      (parent:ParentPreparedInput scope first(source_fork_parent _ _ fork))child_run
      cgroup_binding report_binding channel born after_capabilities queue_after start read_offset read_tick flag path arguments environment,
    prepared_parent_env parent=namespace_initial_env before ->prepared_parent_temps parent=le ->
    PairCapabilityContract pair_primitive ->ForkCapabilityContract fork_primitive ->
    NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
    CapabilityBirth operation groups runs native metadata external can_acquire owner child
      pair_primitive fork_primitive snapshot parent_program channel born ->
    CapabilityHistory operation groups runs native metadata external can_acquire owner child born ticks after_capabilities ->
    SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
    SourceProgramOwner runs owner parent_program ->nth_error runs parent_program=Some run ->
    SourceProgramOwner runs child child_program ->nth_error runs child_program=Some child_run ->
    cursor parent_program=S(length(source_fork_common _ _ fork)) ->cursor child_program=0%nat ->
    worlds parent_program=world ->worlds child_program=namespace_fork_child world snapshot ->
    namespace_queue_steps platform before_world before_queues(source_fork_common _ _ fork)world fork_queues ->
    fork_matches world snapshot ->fork_parent snapshot=physical_identity_task owner ->fork_child snapshot=physical_identity_task child ->
    fork_inherited_table snapshot first=Some(endpoint_binding channel parent_endpoint) ->
    NativeForkCopy(scope_cell scope)(source_fork_before _ _ fork)(source_fork_parent _ _ fork)child_memory ->
    Lean.eq(argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight(scope_borrowed scope))))
      (argument_bytes(map Byte.repr[114;117;110])) ->
    namespace_table before_world(prepared_cgroup_fd parent)=Some cgroup_binding ->
    namespace_table before_world(prepared_report_fd parent)=Some report_binding ->
    source_cell child_run=scope_cell scope ->
    source_before child_run=live(Returnstate(Vint Int.zero)(source_fork_continuation _ _ fork)child_memory) ->
    In(namespace_guest_event(entry_image path arguments environment))(source_events child_run) ->
    (forall offset tick,nth_error ticks offset=Some tick ->SourceIO runs tick) ->
    (forall offset tick,nth_error ticks offset=Some tick ->LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick) ->
    physical_queue_execution channel(fork_queues channel)ticks queue_after ->nth_error ticks read_offset=Some read_tick ->
    Lean.eq(ProcessImport.socket read_tick)(LeanCage_Entry_CallerPhysical_SocketObservation_read child
      (NamespaceHandles.native_descriptor_number failure)(Nat_of_nat 1)physical_grant_bytes) ->
    LeanCage_Entry_CallerPhysical_TickBinding read_tick(LeanCage_Entry_CallerPhysical_taskKey child)
      (NamespaceHandles.native_descriptor_number failure)
      (NamespaceHandles.native_descriptor_object(release_endpoint channel child_endpoint))(physical_flag flag) ->
    inhabited(RecordedForkAdmission operation groups scope first snapshot run fork parent owner child parent_program
      channel ticks start read_offset read_tick).
Proof.
  intros ROOT TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR.
  destruct(actual_prepared_source_common_fork_owned run _ fork before prepared borrowed input output errors le
    ROOT TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR)
    as[peer[pid[pair[first[second[failure[reply[temps[PIPE[PID[FRESH[CONT[LOG FRONTIER]]]]]]]]]]]]].
  pose(scope:={|scope_cell:=source_cell run;
    scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
    scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
    scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|}).
  exists scope,first,second,failure,reply;do 7(split;[reflexivity|]).
  split;[exact PIPE|]. split;[exact PID|]. split;[exact FRESH|].
  intros operation groups runs native metadata external can_acquire pair_primitive fork_primitive platform cursor worlds
    ticks final final_worlds world before_world before_queues fork_queues owner child parent_program child_program child_memory
    parent child_run cgroup_binding report_binding channel born after_capabilities queue_after start read_offset read_tick flag
    path arguments environment ENV TEMPS PAIR FORK NATIVE METADATA BIRTH CAPABILITIES TABLES PARENT_OWNER PARENT_PROGRAM
    CHILD_OWNER CHILD_PROGRAM PARENT_CURSOR CHILD_CURSOR PARENT_WORLD CHILD_WORLD QUEUES MATCH PARENT_ID CHILD_ID PEER COPY MODE
    CGROUP REPORT CHILD_CELL CHILD_START IMAGE SOURCE ORIGINS QUEUE READ_SELECTED READ_SOCKET READ_BINDING.
  assert(ACTUAL_ROOT:source_before run=live(State f_namespace_init(namespace_tail 9)Kstop
    (prepared_parent_env parent)(prepared_parent_temps parent)prepared))by(rewrite ENV,TEMPS;exact ROOT).
  eapply(actual_recorded_fork_admission operation groups runs native metadata external can_acquire pair_primitive fork_primitive
    platform cursor worlds ticks final final_worlds scope first second failure reply world before_world before_queues fork_queues
    snapshot owner child parent_program child_program run fork child_memory parent child_run prepared cgroup_binding report_binding
    channel born after_capabilities queue_after start read_offset read_tick flag path arguments environment);
    try eassumption;reflexivity.
Qed.

(* §FS-entry.release: Actual allocation and source frames supply the complete local caller input. *)
Theorem actual_prepared_recorded_fork_from_raw
    run snapshot(fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    before prepared borrowed input output errors le parentfd report cgroup sequence:
  source_before run=live(State f_namespace_init(namespace_tail 9)Kstop(namespace_initial_env before)le prepared) ->
  Mem.valid_block before(tls_block(source_cell run)) ->
  Forall(Mem.valid_block before)(handoff_borrowed_blocks borrowed) ->
  Mem.valid_block before(namespace_symbol _admission_cgroup) ->
  Mem.valid_block before(namespace_symbol _preflight) ->
  namespace_symbol _admission_cgroup<>tls_block(source_cell run) ->
  Mem.load Mint32 prepared(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  handoff_borrowed_input(source_cell run)prepared borrowed ->
  (forall object position kind permission,Mem.perm(namespace_initial_memory before)object position kind permission ->
    Mem.perm prepared object position kind permission) ->
  le!_error=Some(Vint Int.zero) ->le!_input=Some(Vint input) ->
  le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  le!_parentfd=Some(Vint parentfd) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  cgroup<>input ->cgroup<>output ->cgroup<>errors ->cgroup<>parentfd ->
  exists(scope:ChildScope)(first second failure:int)(reply:ProcessEffects.close_reply)
    (parent:ParentPreparedInput scope first(source_fork_parent _ _ fork)),
    scope_cell scope=source_cell run /\scope_borrowed scope=borrowed /\
    scope_input scope=input /\scope_output scope=output /\scope_errors scope=errors /\
    scope_history scope=[] /\scope_continuation scope=
      namespace_creation_cont(namespace_initial_env before)le Kstop /\
    prepared_parent_env parent=namespace_initial_env before /\prepared_parent_temps parent=le /\
    prepared_parent_fd parent=parentfd /\prepared_report_fd parent=report /\
    prepared_cgroup_fd parent=cgroup /\prepared_sequence parent=sequence /\
    (exists child_temps,
      source_fork_continuation _ _ fork=
        child_fork_cont(storage_pair(scope_storage scope))child_temps(scope_continuation scope) /\
      namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply /\
      ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
        (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork))) /\
    forall operation groups runs native metadata external can_acquire pair_primitive fork_primitive
      (platform:NamespaceQueueContract)cursor worlds ticks final final_worlds world before_world before_queues fork_queues
      owner child parent_program child_program child_memory
      child_run
      cgroup_binding report_binding channel born after_capabilities queue_after start read_offset read_tick flag path arguments environment,
    PairCapabilityContract pair_primitive ->ForkCapabilityContract fork_primitive ->
    NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
    CapabilityBirth operation groups runs native metadata external can_acquire owner child
      pair_primitive fork_primitive snapshot parent_program channel born ->
    CapabilityHistory operation groups runs native metadata external can_acquire owner child born ticks after_capabilities ->
    SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
    SourceProgramOwner runs owner parent_program ->nth_error runs parent_program=Some run ->
    SourceProgramOwner runs child child_program ->nth_error runs child_program=Some child_run ->
    cursor parent_program=S(length(source_fork_common _ _ fork)) ->cursor child_program=0%nat ->
    worlds parent_program=world ->worlds child_program=namespace_fork_child world snapshot ->
    namespace_queue_steps platform before_world before_queues(source_fork_common _ _ fork)world fork_queues ->
    fork_matches world snapshot ->fork_parent snapshot=physical_identity_task owner ->fork_child snapshot=physical_identity_task child ->
    fork_inherited_table snapshot first=Some(endpoint_binding channel parent_endpoint) ->
    NativeForkCopy(scope_cell scope)(source_fork_before _ _ fork)(source_fork_parent _ _ fork)child_memory ->
    Lean.eq(argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight(scope_borrowed scope))))
      (argument_bytes(map Byte.repr[114;117;110])) ->
    namespace_table before_world(prepared_cgroup_fd parent)=Some cgroup_binding ->
    namespace_table before_world(prepared_report_fd parent)=Some report_binding ->
    source_cell child_run=scope_cell scope ->
    source_before child_run=live(Returnstate(Vint Int.zero)(source_fork_continuation _ _ fork)child_memory) ->
    In(namespace_guest_event(entry_image path arguments environment))(source_events child_run) ->
    (forall offset tick,nth_error ticks offset=Some tick ->SourceIO runs tick) ->
    (forall offset tick,nth_error ticks offset=Some tick ->LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick) ->
    physical_queue_execution channel(fork_queues channel)ticks queue_after ->nth_error ticks read_offset=Some read_tick ->
    Lean.eq(ProcessImport.socket read_tick)(LeanCage_Entry_CallerPhysical_SocketObservation_read child
      (NamespaceHandles.native_descriptor_number failure)(Nat_of_nat 1)physical_grant_bytes) ->
    LeanCage_Entry_CallerPhysical_TickBinding read_tick(LeanCage_Entry_CallerPhysical_taskKey child)
      (NamespaceHandles.native_descriptor_number failure)
      (NamespaceHandles.native_descriptor_object(release_endpoint channel child_endpoint))(physical_flag flag) ->
    inhabited(RecordedForkAdmission operation groups scope first snapshot run fork parent owner child parent_program
      channel ticks start read_offset read_tick).
Proof.
  intros ROOT TLS BLOCKS CG_VALID PF_VALID CG_TLS CG_LOAD INPUT PERMISSIONS ERROR IN OUT ERR
    PARENT REPORT SEQUENCE CG_IN CG_OUT CG_ERR CG_PARENT.
  destruct(actual_prepared_source_common_fork_owned run _ fork before prepared borrowed input output errors le
    ROOT TLS BLOCKS INPUT PERMISSIONS ERROR IN OUT ERR)
    as[peer[pid[pair[first[second[failure[reply[temps[PIPE[PID[FRESH[CONT[LOG FRONTIER]]]]]]]]]]]]].
  pose(scope:={|scope_cell:=source_cell run;
    scope_storage:={|storage_pair:=pair;storage_peer:=peer;storage_pid:=pid|};
    scope_borrowed:=borrowed;scope_input:=input;scope_output:=output;scope_errors:=errors;
    scope_continuation:=namespace_creation_cont(namespace_initial_env before)le Kstop;scope_history:=[]|}).
  change(ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
    (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)))in FRONTIER.
  change(namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply)in LOG.
  change(source_fork_continuation _ _ fork=child_fork_cont pair temps(scope_continuation scope))in CONT.
  assert(SHAPED:ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[](child_fork_cont pair temps(scope_continuation scope))
      (source_fork_before _ _ fork)))by(rewrite <-CONT,<-LOG;exact FRONTIER).
  destruct(actual_common_fork_inputs _ _ _ _ _ _ _ SHAPED)as[REGISTERS[FAILURE[NONNEGATIVE REST]]].
  assert(SUCCESS:Forall prepared_setup_success(namespace_fd_events(source_fork_common _ _ fork))).
  { rewrite LOG;apply prepared_signal_log_success;[reflexivity|exact NONNEGATIVE]. }
  pose proof(actual_prepared_parent_cgroup_load run _ fork before prepared borrowed input output errors le
    (namespace_symbol _admission_cgroup)(Vint cgroup)ROOT TLS BLOCKS CG_VALID CG_TLS CG_LOAD INPUT PERMISSIONS
    ERROR IN OUT ERR SUCCESS)as CG_PARENT_LOAD.
  assert(CG_PREPARED:Mem.valid_block prepared(namespace_symbol _admission_cgroup)).
  { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
      [eapply Mem.load_valid_access;exact CG_LOAD|constructor]. }
  destruct(namespace_actual_parent_storage before prepared(source_fork_parent _ _ fork)scope first le parentfd report cgroup sequence
    (Logic.eq_refl _)PIPE PID FRESH TLS CG_VALID PF_VALID CG_PREPARED CG_TLS CG_PARENT_LOAD IN OUT ERR PARENT REPORT SEQUENCE
    CG_IN CG_OUT CG_ERR CG_PARENT)as[parent[ENV[TEMPS[PFD[RFD[CGFD SEQ]]]]]].
  exists scope,first,second,failure,reply,parent;do 7(split;[reflexivity|]).
  split;[exact ENV|]. split;[exact TEMPS|]. split;[exact PFD|]. split;[exact RFD|].
  split;[exact CGFD|]. split;[exact SEQ|].
  split.
  { exists temps;split;[exact CONT|]. split;[exact LOG|exact FRONTIER]. }
  intros operation groups runs native metadata external can_acquire pair_primitive fork_primitive platform cursor worlds
    ticks final final_worlds world before_world before_queues fork_queues owner child parent_program child_program child_memory
    child_run cgroup_binding report_binding channel born after_capabilities queue_after start read_offset read_tick flag
    path arguments environment PAIR FORK NATIVE METADATA BIRTH CAPABILITIES TABLES PARENT_OWNER PARENT_PROGRAM
    CHILD_OWNER CHILD_PROGRAM PARENT_CURSOR CHILD_CURSOR PARENT_WORLD CHILD_WORLD QUEUES MATCH PARENT_ID CHILD_ID PEER COPY MODE
    CGROUP REPORTING CHILD_CELL CHILD_START IMAGE SOURCE ORIGINS QUEUE READ_SELECTED READ_SOCKET READ_BINDING.
  assert(ACTUAL_ROOT:source_before run=live(State f_namespace_init(namespace_tail 9)Kstop
    (prepared_parent_env parent)(prepared_parent_temps parent)prepared))by(rewrite ENV,TEMPS;exact ROOT).
  eapply(actual_recorded_fork_admission operation groups runs native metadata external can_acquire pair_primitive fork_primitive
    platform cursor worlds ticks final final_worlds scope first second failure reply world before_world before_queues fork_queues
    snapshot owner child parent_program child_program run fork child_memory parent child_run prepared cgroup_binding report_binding
    channel born after_capabilities queue_after start read_offset read_tick flag path arguments environment);
    try eassumption;reflexivity.
Qed.
