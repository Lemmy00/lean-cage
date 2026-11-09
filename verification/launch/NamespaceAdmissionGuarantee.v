(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Compose one recorded fork, actual byte transport, and the checked parent authorization. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Clight.
From LeanImport Require Import Lean.
Require Import IO Machine ArgumentsImport.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput NativeHandoffWire NativeValues.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessSourceRecording ProcessSourceTables
  ProcessCapabilityRecording ProcessCapabilityBirth ProcessReleaseSafety.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceMachine NamespaceMemory NamespacePaths NamespaceCaller
  NamespaceStructure NamespaceTraceRegion NamespaceChildResult NamespaceForkPrefix NamespaceFork NamespaceForkInputs NamespaceSourceFork
  NamespaceGrantInputs NamespaceForkGrant NamespaceSocket NamespacePhysical NamespaceChannel NamespaceGrant NamespaceQueue
  NamespaceSourceOwnership NamespaceWriteOrigin NamespaceChildWrites NamespaceReadGrant NamespacePhysicalGrant
  NamespaceParentEntry NamespaceParentSafety NamespaceGuestFlags NamespaceTLS.
Import ListNotations.
Local Close Scope lean_scope.

Record RecordedForkAdmission operation groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick:Type:={
  recorded_send_offset:nat;
  recorded_send_tick:LeanCage_Entry_CallerPhysical_Tick;
  recorded_send_lost:bool;
  recorded_send_selected:nth_error ticks recorded_send_offset=Some recorded_send_tick;
  recorded_send_projection:physical_tick_projection channel recorded_send_tick=
    (physical_tick_table recorded_send_tick,
      channel_sent(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))first[Byte.repr 165]recorded_send_lost);
  recorded_source_ordinal:nat;
  recorded_source_event:namespace_event;
  recorded_source_io:SourceSocketIO;
  recorded_source_selected:nth_error(source_events run)recorded_source_ordinal=Some recorded_source_event;
  recorded_source_socket:namespace_socket_io recorded_source_event=Some recorded_source_io;
  recorded_source_reference:LeanCage_Entry_CallerPhysical_Tick_source recorded_send_tick=
    source_reference program recorded_source_ordinal;
  recorded_source_peer:descriptor(source_socket_request recorded_source_io)=first;
  recorded_source_count:requested(source_socket_request recorded_source_io)=1;
  recorded_source_bytes:source_socket_bytes recorded_source_io=[Byte.repr 165];
  recorded_source_loss:source_socket_lost recorded_source_io=recorded_send_lost;
  recorded_finish_prefix:list namespace_event;
  recorded_setup_prefix:list namespace_event;
  recorded_ready:mem;
  recorded_ready_tls:Mem.valid_block recorded_ready(tls_block(scope_cell scope));
  recorded_grant_prefix:list namespace_event;
  recorded_release_prefix:list namespace_event;
  recorded_source_order:firstn(recorded_source_ordinal-S(length(source_fork_common _ _ fork)))(source_fork_body _ _ fork)=
    recorded_finish_prefix++recorded_setup_prefix++recorded_grant_prefix++recorded_release_prefix;
  recorded_closed_failure:int;
  recorded_closed_failure_child:fork_inherited_table snapshot recorded_closed_failure=
    Some(endpoint_binding channel child_endpoint);
  recorded_setup_closes:Forall(namespace_parent_closes_from[recorded_closed_failure;scope_input scope;scope_output scope;
    scope_errors scope;prepared_parent_fd input])(recorded_finish_prefix++recorded_setup_prefix);
  recorded_setup_quiet:Forall(fun event=>namespace_parent_prelude_event event=true)(recorded_finish_prefix++recorded_setup_prefix);
  recorded_actual_setup:namespace_steps ProcessGlobalCalls.caller_ge(source_cell run)
    (live(Returnstate(Vint(task_pid(fork_child snapshot)))(source_fork_continuation _ _ fork)(source_fork_parent _ _ fork)))
    (recorded_finish_prefix++recorded_setup_prefix)
    (live(State f_namespace_init(namespace_tail 20)Kstop(prepared_parent_env input)
      (namespace_parent_setup_env(prepared_parent_temps input)(task_pid(fork_child snapshot)))recorded_ready));
  recorded_parent_authorized:namespace_authorized_parent(scope_cell scope)recorded_ready(task_pid(fork_child snapshot))first
    (prepared_cgroup_fd input)(prepared_status_cell input)(prepared_result_temporary input)(prepared_admission_cell input)
    (prepared_report_fd input)(prepared_sequence input)recorded_grant_prefix;
  recorded_source_resume:nat;
  recorded_source_resumed:nth_error(source_events run)recorded_source_resume=
    Some(namespace_process(release_resume_event(task_pid(fork_child snapshot))));
  recorded_grant_before_resume:(S(length(source_fork_common _ _ fork))+length recorded_finish_prefix+
    length recorded_setup_prefix+length recorded_grant_prefix<=recorded_source_resume)%nat;
  recorded_source_resume_order:(S(length(source_fork_common _ _ fork))<=recorded_source_resume<recorded_source_ordinal)%nat;
  recorded_resume_offset:nat;
  recorded_resume_tick:LeanCage_Entry_CallerPhysical_Tick;
  recorded_resume_snapshot:SourceSnapshot;
  recorded_resume_selected:nth_error ticks recorded_resume_offset=Some recorded_resume_tick;
  recorded_resume_reference:LeanCage_Entry_CallerPhysical_Tick_source recorded_resume_tick=source_reference program recorded_source_resume;
  recorded_resume_primitive:SourcePrimitive operation groups child owner
    (namespace_process(release_resume_event(task_pid(fork_child snapshot))))recorded_resume_tick recorded_resume_snapshot;
  recorded_resume_action:LeanCage_Entry_CallerPhysical_Tick_action recorded_resume_tick=
    LeanCage_Entry_CallerPhysical_Action_request owner(Nat_of_nat 7)(Nat_of_nat 0);
  recorded_physical_order:(recorded_resume_offset<recorded_send_offset<read_offset)%nat;
  recorded_read_selected:nth_error ticks read_offset=Some read_tick;
  recorded_read_at:LeanCage_Entry_CallerPhysical_TickAt(tick_values ticks)(Nat_of_nat read_offset)read_tick;
  recorded_send_at:LeanCage_Entry_CallerPhysical_TickAt(tick_values ticks)(Nat_of_nat recorded_send_offset)recorded_send_tick;
  recorded_resume_at:LeanCage_Entry_CallerPhysical_TickAt(tick_values ticks)(Nat_of_nat recorded_resume_offset)recorded_resume_tick;
  recorded_grant_before_read:LeanCage_Entry_PhysicalHandoff_grantBeforeRead
    (Nat_of_nat(start+recorded_send_offset))(Nat_of_nat(start+read_offset))
}.

Arguments recorded_send_offset {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_send_tick {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_send_lost {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_send_selected {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_send_projection {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_ordinal {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_event {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_io {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_selected {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_socket {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_reference {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_peer {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_count {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_bytes {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_loss {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_finish_prefix {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_setup_prefix {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_ready {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_ready_tls {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_grant_prefix {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_release_prefix {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_order {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_setup_quiet {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_closed_failure {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_closed_failure_child {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_setup_closes {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_actual_setup {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_parent_authorized {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_resume {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_resumed {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_grant_before_resume {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_source_resume_order {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_resume_offset {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_resume_tick {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_resume_snapshot {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_resume_selected {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_resume_reference {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_resume_primitive {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_resume_action {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_physical_order {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_read_selected {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_read_at {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_send_at {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_resume_at {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.
Arguments recorded_grant_before_read {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick} _.

Theorem actual_recorded_fork_admission operation groups runs native metadata external can_acquire
    pair_primitive fork_primitive(platform:NamespaceQueueContract)cursor worlds ticks final final_worlds
    scope first second failure reply world before_world before_queues fork_queues snapshot owner child parent_program child_program
    run(fork:ActualSourceFork run(task_pid(fork_child snapshot)))child_memory
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))child_run prepared_memory
    cgroup_binding report_binding channel born after_capabilities queue_after start read_offset read_tick flag path arguments environment:
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
  scope_history scope=[] ->source_cell run=scope_cell scope ->
  source_before run=live(State f_namespace_init(namespace_tail 9)Kstop(prepared_parent_env input)(prepared_parent_temps input)prepared_memory) ->
  ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
    (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)) ->
  namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply ->
  namespace_queue_steps platform before_world before_queues(source_fork_common _ _ fork)world fork_queues ->
  fork_matches world snapshot ->fork_parent snapshot=physical_identity_task owner ->fork_child snapshot=physical_identity_task child ->
  fork_inherited_table snapshot first=Some(endpoint_binding channel parent_endpoint) ->
  NativeForkCopy(scope_cell scope)(source_fork_before _ _ fork)(source_fork_parent _ _ fork)child_memory ->
  Lean.eq(argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight(scope_borrowed scope))))
    (argument_bytes(map Byte.repr[114;117;110])) ->
  namespace_table before_world(prepared_cgroup_fd input)=Some cgroup_binding ->
  namespace_table before_world(prepared_report_fd input)=Some report_binding ->
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
  inhabited(RecordedForkAdmission operation groups scope first snapshot run fork input owner child parent_program
    channel ticks start read_offset read_tick).
Proof.
  intros PAIR FORK NATIVE METADATA BIRTH CAPABILITIES TABLES PARENT_OWNER PARENT_PROGRAM CHILD_OWNER CHILD_PROGRAM
    PARENT_CURSOR CHILD_CURSOR PARENT_WORLD CHILD_WORLD HISTORY CELL ROOT FRONTIER LOG QUEUES MATCH PARENT_ID CHILD_ID
    PEER COPY MODE CGROUP REPORT CHILD_CELL CHILD_START IMAGE SOURCE ORIGINS QUEUE READ_SELECTED READ_SOCKET READ_BINDING.
  assert(KERNEL:NamespaceWorldTrace.namespace_kernel_steps before_world(source_fork_common _ _ fork)world)
    by(eapply namespace_queue_steps_kernel;exact QUEUES).
  assert(FRONTIER_LOG:ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)))
    by(rewrite <-LOG;exact FRONTIER).
  destruct(actual_common_fork_continuation _ _ _ _ _ _ _ FRONTIER_LOG)as[temps CONT].
  assert(SHAPED_FRONTIER:ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
    (Callstate namespace_fork_definition[](child_fork_cont(storage_pair(scope_storage scope))temps(scope_continuation scope))
      (source_fork_before _ _ fork)))by(rewrite <-CONT;exact FRONTIER).
  assert(SHAPED_LOG:ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[](child_fork_cont(storage_pair(scope_storage scope))temps(scope_continuation scope))
      (source_fork_before _ _ fork)))by(rewrite <-CONT;exact FRONTIER_LOG).
  pose proof(source_fork_prefix _ _ fork)as COMMON_SOURCE.
  rewrite CELL,CONT in COMMON_SOURCE.
  destruct(actual_common_fork_has_empty_channel platform scope(source_before run)(source_fork_common _ _ fork)
    before_world before_queues world fork_queues first second failure reply temps(source_fork_before _ _ fork)
    HISTORY SHAPED_FRONTIER LOG COMMON_SOURCE QUEUES)
    as[created[inherited[WORLD_CREATED[PARENT_ENDPOINT[CHILD_ENDPOINT EMPTY]]]]].
  assert(WORLD_TABLE:namespace_table world=inherited).
  { rewrite WORLD_CREATED;unfold NamespaceWorldTrace.child_fork_world,namespace_default_action;rewrite Int.eq_true;reflexivity. }
  assert(TABLE_PEER:namespace_table world first=Some(endpoint_binding channel parent_endpoint)).
  { destruct MATCH as[MP[MT INHERITED]];rewrite <-INHERITED;exact PEER. }
  rewrite WORLD_TABLE,PARENT_ENDPOINT in TABLE_PEER;unfold endpoint_binding in TABLE_PEER;inversion TABLE_PEER;subst created.
  rewrite EMPTY in QUEUE.
  assert(CHILD_SOURCE:namespace_steps namespace_ge(scope_cell scope)
    (live(Returnstate(Vint Int.zero)(child_fork_cont(storage_pair(scope_storage scope))temps(scope_continuation scope))child_memory))
    (source_events child_run)(source_after child_run)).
  { pose proof(source_executed child_run)as RUN;rewrite CHILD_CELL,CHILD_START,CONT in RUN;exact RUN. }
  assert(PROFILE:Forall(fun event=>NamespaceDescriptorFrame.namespace_after_fork_event event=true)(source_events child_run)).
  { eapply actual_child_image_source_has_no_capability_export;[exact HISTORY|exact SHAPED_LOG|exact MATCH|
      exact COPY|exact CHILD_SOURCE|exact IMAGE]. }
  assert(WRITES:forall event io,In event(source_events child_run) ->namespace_socket_io event=Some io ->
    IO.operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=failure).
  { eapply actual_child_branch_write_descriptors;[exact HISTORY|exact SHAPED_LOG|exact MATCH|
      exact COPY|exact CHILD_SOURCE|exact IMAGE]. }
  assert(FAILURE:excludes_parent_at(namespace_table(worlds child_program))channel failure).
  { rewrite CHILD_WORLD;change(excludes_parent_at(namespace_table world)channel failure).
    rewrite WORLD_TABLE;intros binding PRESENT OBJECT;rewrite CHILD_ENDPOINT in PRESENT;inversion PRESENT;subst;discriminate. }
  assert(NONNEGATIVE:(0<=Int.signed failure)%Z).
  { destruct(actual_common_fork_inputs _ _ _ _ _ _ _ ltac:(exact SHAPED_LOG))as[REG[FD[VALID REST]]];exact VALID. }
  destruct(actual_bound_read_parent_source_send operation groups runs cursor worlds ticks final final_worlds owner child
    child_program child_run channel failure queue_after start read_offset read_tick failure flag
    TABLES CHILD_OWNER CHILD_PROGRAM SOURCE ORIGINS
    ltac:(intros offset tick actor SELECTED OTHER;eapply capability_birth_foreign_absence;eassumption)
    PROFILE WRITES FAILURE QUEUE READ_SELECTED READ_SOCKET NONNEGATIVE READ_BINDING)
    as[send_offset[sent_tick[source_fd[bytes[lost SEND_FACTS]]]]].
  destruct SEND_FACTS as[SEND_SELECTED[SEND_BEFORE[PROJECT[[binding[PRESENT OBJECT]][REFERENCE[BYTE ORDER]]]]]].
  assert(TABLE_PEER':namespace_table world first=Some(endpoint_binding channel parent_endpoint))by(rewrite WORLD_TABLE;exact PARENT_ENDPOINT).
  assert(FAILURE_CHILD:fork_inherited_table snapshot failure=Some(endpoint_binding channel child_endpoint)).
  { destruct MATCH as[MP[MT INHERITED]];rewrite INHERITED,WORLD_TABLE;exact CHILD_ENDPOINT. }
  destruct(actual_same_fork_physical_send_authorized operation groups runs cursor worlds ticks final final_worlds
    scope first second failure reply world before_world snapshot owner child parent_program run fork child_memory input
    cgroup_binding report_binding channel send_offset sent_tick source_fd bytes lost binding
    TABLES PARENT_OWNER PARENT_PROGRAM PARENT_CURSOR PARENT_WORLD HISTORY CELL FRONTIER LOG KERNEL MATCH CHILD_ID COPY MODE
    CGROUP REPORT TABLE_PEER' SEND_SELECTED(SOURCE _ _ SEND_SELECTED)REFERENCE PROJECT PRESENT OBJECT)
    as[source_ordinal[event[io[finish_prefix[setup_prefix[ready[grant_prefix[release_prefix[resume[resume_offset[resume_tick[resume_snapshot FACTS]]]]]]]]]]]].
  destruct FACTS as[QUIET[CLOSED[FD[EVENT[SOCKET[IO_FD[IO_BYTES[IO_LOST[SEND_REFERENCE[TRACE[SETUP[AUTHORIZED[RESUMED[GRANT_BEFORE_RESUME[RESUME_BEFORE
    [COUNT[CONTENT[RESUME_SELECTED[RESUME_OFFSET[RESUME_REFERENCE[PRIMITIVE ACTION]]]]]]]]]]]]]]]]]]]]].
  assert(EXACT_BYTES:bytes=[Byte.repr 165])by congruence.
  assert(PARENT_TLS:Mem.valid_block(source_fork_parent _ _ fork)(tls_block(scope_cell scope))).
  { destruct(same_fork_parent_borrowed_inputs _ _ _ _ _ _ _ _ _ SHAPED_LOG COPY)as[BORROWED REST].
    apply namespace_errno_ready_valid;exact(handoff_borrowed_errno _ _ _ BORROWED). }
  assert(READY_TLS:Mem.valid_block ready(tls_block(scope_cell scope))).
  { assert(INITIAL_TLS:Mem.valid_block(source_fork_parent _ _ fork)(tls_block(source_cell run)))
      by(rewrite CELL;exact PARENT_TLS).
    pose proof(namespace_steps_tls_valid ProcessGlobalCalls.caller_ge(source_cell run)_ _ _ SETUP INITIAL_TLS)as READY.
    change(Mem.valid_block ready(tls_block(source_cell run)))in READY;rewrite CELL in READY;exact READY. }
  assert(IO_PEER:descriptor(source_socket_request io)=first)by congruence.
  assert(EXACT_PROJECTION:physical_tick_projection channel sent_tick=
    (physical_tick_table sent_tick,channel_sent(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
      first[Byte.repr 165]lost)).
  { rewrite <-FD,<-EXACT_BYTES;exact PROJECT. }
  constructor;refine{|recorded_send_offset:=send_offset;recorded_send_tick:=sent_tick;recorded_send_lost:=lost;
    recorded_source_ordinal:=source_ordinal;recorded_source_event:=event;recorded_source_io:=io;
    recorded_closed_failure:=failure;recorded_finish_prefix:=finish_prefix;recorded_setup_prefix:=setup_prefix;recorded_ready:=ready;
    recorded_grant_prefix:=grant_prefix;recorded_release_prefix:=release_prefix;recorded_source_resume:=resume;
    recorded_resume_offset:=resume_offset;recorded_resume_tick:=resume_tick;recorded_resume_snapshot:=resume_snapshot|};try assumption.
  - split;assumption.
  - eapply actual_tick_position;exact READ_SELECTED.
  - eapply actual_tick_position;exact SEND_SELECTED.
  - eapply actual_tick_position;exact RESUME_SELECTED.
  - destruct ORDER as[ORDER];exact ORDER.
Qed.
