(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.receipt: Derive public scope from the actual caller and same journal. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
From LeanImport Require Import Lean.
Require Import IO Machine ArgumentsImport.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput NativeHandoffWire NativeValues.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessJournalLiveness ProcessOwnership
  ProcessPhysicalTrace ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds ProcessScope ProcessScopeRecording ProcessCgroupRecording
  ProcessCapabilityRecording ProcessCapabilityBirth.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceMachine NamespaceMemory NamespacePaths NamespaceCaller
  NamespaceChildResult NamespaceForkPrefix NamespaceFork NamespaceForkInputs NamespaceSourceFork NamespaceGrantInputs NamespaceQueue
  NamespacePhysical NamespaceHandles NamespaceChannel NamespaceTraceRegion NamespaceAdmissionGuarantee NamespacePublicReceipt
  NamespaceApplicationPositions NamespaceScopeBridge NamespaceSourceCgroup NamespaceChildCgroup NamespaceCapabilities NamespaceGuestFlags
  NamespaceCgroupAuthority NamespaceSourceOwnership NamespacePreparedAdmission NamespacePrepared NamespaceDescriptorFrame
  NamespaceDescriptorOrigin.
Import ListNotations.
Local Close Scope lean_scope.

Lemma scope_selected_property ticks offset tick(P:LeanCage_Entry_CallerPhysical_Tick->SProp):
  (forall actual,nth_error ticks(nat_of_Nat offset)=Some actual ->P actual) ->
  LeanCage_Entry_CallerPhysical_TickAt(tick_values ticks)offset tick ->P tick.
Proof.
  intros PROPERTY AT;pose proof(journal_selected_value ticks offset tick AT)as SELECTED.
  destruct(nth_error ticks(nat_of_Nat offset))as[actual|]eqn:ACTUAL;[|destruct SELECTED].
  exact(journal_strict_transport _ P actual tick SELECTED(PROPERTY actual(Logic.eq_refl _))).
Qed.

Record SourceScopeProduction owner child start limit ticks group failure channel groups:Type:={
  source_scope_produced:LeanCage_Entry_SourceScopeProducer owner child(Nat_of_nat start)limit(tick_values ticks)
    (Nat_of_nat group)(native_descriptor_number failure)(native_descriptor_object(release_endpoint channel child_endpoint))
    (recorded_cgroup_objects groups)
}.

Arguments source_scope_produced {owner child start limit ticks group failure channel groups} _.

Theorem actual_fork_source_scope_producer operation(linux:LinuxProcessContract operation)groups runs native metadata external
    can_acquire pair_primitive fork_primitive(platform:NamespaceQueueContract)cursor worlds ticks final final_worlds
    scope first second failure reply world before_world before_queues fork_queues snapshot owner child parent_program child_program
    run(fork:ActualSourceFork run(task_pid(fork_child snapshot)))child_memory
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))child_run prepared_memory
    cgroup_binding report_binding channel capabilities_before after_capabilities queue_after start limit path arguments environment
    child_temps process_before_fork process_after_fork other process_after group mayTrace history namespace initial_group context:
  PairCapabilityContract pair_primitive ->ForkCapabilityContract fork_primitive ->
  NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
  CapabilityBirth operation groups runs native metadata external can_acquire owner child
    pair_primitive fork_primitive snapshot parent_program channel capabilities_before ->
  CapabilityHistory operation groups runs native metadata external can_acquire owner child capabilities_before ticks after_capabilities ->
  SourceProgramOwner runs owner parent_program ->nth_error runs parent_program=Some run ->
  SourceProgramOwner runs child child_program ->nth_error runs child_program=Some child_run ->
  cursor parent_program=S(length(source_fork_common _ _ fork)) ->cursor child_program=0%nat ->
  worlds parent_program=world ->worlds child_program=namespace_fork_child world snapshot ->
  scope_history scope=[] ->source_cell run=scope_cell scope ->
  source_before run=live(State f_namespace_init(namespace_tail 9)Kstop(prepared_parent_env input)(prepared_parent_temps input)prepared_memory) ->
  ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
    (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)) ->
  namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply ->
  source_fork_continuation _ _ fork=child_fork_cont(storage_pair(scope_storage scope))child_temps(scope_continuation scope) ->
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
  physical_queue_execution channel(fork_queues channel)ticks queue_after ->
  SourceOtherContract other groups(physical_identity_task owner)(physical_identity_task child) ->
  SourceProcessSchedule operation groups child runs parent_program other cursor worlds process_after_fork ticks final final_worlds process_after ->
  ForkProcessEffect(worlds parent_program)process_before_fork snapshot process_after_fork ->
  namespace_sigchld(worlds parent_program)=default_signal_action ->
  process_sole_waiter process_before_fork(fork_parent snapshot)=true ->
  SourceFileView groups process_after_fork(physical_identity_task owner)(worlds parent_program) ->
  process_cgroup_files process_after_fork(physical_identity_task owner)(prepared_cgroup_fd input)=Some group ->
  PreparedCgroupHandles groups(namespace_table(worlds parent_program))(prepared_cgroup_fd input) ->
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child history
    (LeanCage_Entry_CallerPhysical_born namespace initial_group)(tick_values ticks)context ->
  (forall offset tick,nth_error ticks offset=Some tick ->PlacementRecording groups tick) ->
  (forall offset tick,nth_error ticks offset=Some tick ->forall actor,
    unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)) ->
    forall object assigned,groups object=Some assigned ->
      object_absent(physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)))(ordinary_object object)) ->
  LeanCage_Entry_SourceScopeProducer owner child(Nat_of_nat start)limit(tick_values ticks)(Nat_of_nat group)
    (native_descriptor_number failure)(native_descriptor_object(release_endpoint channel child_endpoint))
    (recorded_cgroup_objects groups).
Proof.
  intros PAIR FORK NATIVE METADATA BIRTH CAPABILITIES PARENT_OWNER PARENT_PROGRAM CHILD_OWNER CHILD_PROGRAM
    PARENT_CURSOR CHILD_CURSOR PARENT_WORLD CHILD_WORLD HISTORY CELL ROOT FRONTIER LOG CONT QUEUES MATCH PARENT_ID CHILD_ID
    PEER COPY MODE CGROUP REPORT CHILD_CELL CHILD_START IMAGE IO ORIGINS QUEUE OTHER PROCESS FORK_PROCESS DEFAULT SOLE FILES FILE
    HANDLES JOURNAL PLACEMENTS FOREIGN.
  pose proof(source_process_schedule_tables _ _ _ _ _ _ _ _ _ _ _ _ _ PROCESS)as TABLES.
  assert(SHAPED:ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[](child_fork_cont(storage_pair(scope_storage scope))child_temps(scope_continuation scope))
      (source_fork_before _ _ fork)))by(rewrite <-LOG,<-CONT;exact FRONTIER).
  assert(FAILURE:fork_inherited_table snapshot failure=Some(endpoint_binding channel child_endpoint)).
  { eapply(actual_common_fork_failure_endpoint scope(source_fork_common _ _ fork)before_world world first second failure reply
      child_temps(source_fork_before _ _ fork)snapshot channel);try eassumption.
    - rewrite <-CONT;exact FRONTIER.
    - eapply namespace_queue_steps_kernel;exact QUEUES. }
  assert(CHILD_WRITES:forall offset tick ordinal,nth_error ticks offset=Some tick ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference child_program ordinal ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick).
  { intros offset tick ordinal SELECTED SOURCE.
    eapply(actual_same_fork_child_write_outside_cgroup operation groups child runs cursor worlds ticks final final_worlds
      scope first second failure reply child_temps(source_fork_before _ _ fork)world snapshot(source_fork_parent _ _ fork)
      child_memory child_run child_program offset tick ordinal channel path arguments environment);try eassumption.
    - rewrite <-CONT;exact CHILD_START.
    - exact(IO offset tick SELECTED). }
  assert(FOREIGN_ABSENT:forall offset tick,nth_error ticks offset=Some tick ->forall actor,
    nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)<>nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner) ->
    nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)<>nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child) ->
    LeanCage_Entry_CallerPhysical_CgroupAbsent(recorded_cgroup_objects groups)tick actor).
  { intros offset tick SELECTED actor NOT_PARENT NOT_CHILD;apply actual_cgroup_absence_produces_ordinary.
    apply(FOREIGN offset tick SELECTED actor);split;assumption. }
  assert(OTHER_QUIET:forall tick,In tick ticks ->
    (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference parent_program ordinal) ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick).
  { intros tick MEMBER NOT_PARENT;apply In_nth_error in MEMBER;destruct MEMBER as[offset SELECTED].
    eapply(actual_source_writer_cgroup_classification groups runs owner child parent_program child_program tick);
      [exact PARENT_OWNER|exact CHILD_OWNER|exact(IO offset tick SELECTED)|exact(ORIGINS offset tick SELECTED)| | |].
    - intros ordinal SOURCE;contradiction(NOT_PARENT ordinal SOURCE).
    - intros ordinal SOURCE;exact(CHILD_WRITES offset tick ordinal SELECTED SOURCE).
    - exact(FOREIGN_ABSENT offset tick SELECTED). }
  intros read_offset read_tick flag READ_AT READ_SOCKET READ_BINDING.
  remember(nat_of_Nat read_offset)as index eqn:INDEX.
  assert(OFFSET:Nat_of_nat index=read_offset)by(rewrite INDEX;apply Nat2natid).
  subst read_offset.
  pose proof(journal_selected_value ticks(Nat_of_nat index)read_tick READ_AT)as ACTUAL.
  rewrite nat2Natid in ACTUAL.
  destruct(nth_error ticks index)as[current|]eqn:SELECTED;[|destruct ACTUAL].
  assert(SOCKET:Lean.eq(ProcessImport.socket current)(LeanCage_Entry_CallerPhysical_SocketObservation_read child
    (native_descriptor_number failure)(Nat_of_nat 1)physical_grant_bytes)).
  { exact(journal_strict_transport _ (fun tick=>Lean.eq(ProcessImport.socket tick)
      (LeanCage_Entry_CallerPhysical_SocketObservation_read child(native_descriptor_number failure)
        (Nat_of_nat 1)physical_grant_bytes))read_tick current(journal_strict_sym _ _ _ ACTUAL)READ_SOCKET). }
  assert(BINDING:LeanCage_Entry_CallerPhysical_TickBinding current(LeanCage_Entry_CallerPhysical_taskKey child)
    (native_descriptor_number failure)(native_descriptor_object(release_endpoint channel child_endpoint))flag).
  { exact(journal_strict_transport _ (fun tick=>LeanCage_Entry_CallerPhysical_TickBinding tick
      (LeanCage_Entry_CallerPhysical_taskKey child)(native_descriptor_number failure)
      (native_descriptor_object(release_endpoint channel child_endpoint))flag)
      read_tick current(journal_strict_sym _ _ _ ACTUAL)READ_BINDING). }
  assert(FLAG:exists actual,physical_flag actual=flag)by(destruct flag;[exists false|exists true];reflexivity).
  destruct FLAG as[actual_flag FLAG];rewrite <-FLAG in BINDING.
  assert(RECORDED:inhabited(RecordedForkAdmission operation groups scope first snapshot run fork input owner child parent_program
    channel ticks start index current)).
  { eapply(actual_recorded_fork_admission operation groups runs native metadata external can_acquire pair_primitive fork_primitive
      platform cursor worlds ticks final final_worlds scope first second failure reply world before_world before_queues fork_queues
      snapshot owner child parent_program child_program run fork child_memory input child_run prepared_memory cgroup_binding report_binding
      channel capabilities_before after_capabilities queue_after start index current actual_flag path arguments environment);eassumption. }
  destruct RECORDED as[recorded].
  assert(PUBLIC:inhabited(PublicSourceReceipt operation groups scope first snapshot run fork input owner child parent_program
    channel ticks start index current recorded group)).
  { eapply(recorded_fork_public_source_from_journal operation linux groups scope first snapshot run fork input owner child parent_program
      channel ticks start index current recorded runs cursor worlds process_before_fork process_after_fork other final final_worlds
      process_after group child_temps mayTrace history namespace initial_group context);eassumption. }
  destruct PUBLIC as[public].
  pattern read_tick.
  eapply(journal_strict_transport _ _ current read_tick ACTUAL).
  exists(public_scope_inputs operation groups scope first snapshot run fork input owner child parent_program channel ticks start index current
    recorded group public).
  constructor.
  - intros offset tick LOWER UPPER AT.
    eapply(scope_selected_property ticks offset tick
      (fun actual=>LeanCage_Entry_CallerPhysical_PlacementRecording(recorded_cgroup_objects groups)actual));[|exact AT].
    intros actual ACTUAL_SELECTED;apply actual_placement_produces_ordinary;exact(PLACEMENTS _ _ ACTUAL_SELECTED).
  - constructor.
    + intros offset tick LOWER UPPER AT reference SOURCE.
      assert(AFTER:(application_close_offset(public_source_positions public)<nat_of_Nat offset)%nat).
      { pose proof(Nat_le_nat_le' _ _ LOWER)as ORDER.
        change((nat_of_Nat
          (Nat_add (Nat_add (Nat_of_nat start) (Nat_of_nat (application_close_offset (public_source_positions public))))
            (Nat_of_nat 1)) <=nat_of_Nat (Nat_add (Nat_of_nat start) offset))%nat)in ORDER.
        rewrite !physical_add_exact,!nat2Natid in ORDER;lia. }
      eapply(scope_selected_property ticks offset tick
        (fun actual=>LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)actual));[|exact AT].
      intros actual ACTUAL_SELECTED.
      eapply(actual_source_writer_cgroup_classification groups runs owner child parent_program child_program actual);
        [exact PARENT_OWNER|exact CHILD_OWNER|exact(IO _ _ ACTUAL_SELECTED)|exact(ORIGINS _ _ ACTUAL_SELECTED)| | |].
      * intros ordinal REFERENCE;exact(public_source_parent_writes public _ _ _ ACTUAL_SELECTED AFTER REFERENCE).
      * intros ordinal REFERENCE;exact(CHILD_WRITES _ _ _ ACTUAL_SELECTED REFERENCE).
      * exact(FOREIGN_ABSENT _ _ ACTUAL_SELECTED).
    + intros offset tick LOWER UPPER AT actor NOT_PARENT NOT_CHILD.
      eapply(scope_selected_property ticks offset tick
        (fun actual=>LeanCage_Entry_CallerPhysical_CgroupAbsent(recorded_cgroup_objects groups)actual actor));[|exact AT].
      intros actual ACTUAL_SELECTED;apply(FOREIGN_ABSENT _ _ ACTUAL_SELECTED actor).
      * intro SAME;apply actual_task_key_injective in SAME;subst actor;destruct(NOT_PARENT(Lean.eq_refl owner)).
      * intro SAME;apply actual_task_key_injective in SAME;subst actor;destruct(NOT_CHILD(Lean.eq_refl child)).
Qed.

(* §FS-entry.release: Raw preparation selects the actual descriptors before consuming a read. *)
Theorem actual_prepared_source_scope_from_raw
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
  exists(first failure:int),SourceDescriptorOrigin run _ fork first failure /\
  forall operation(linux:LinuxProcessContract operation)groups runs native metadata external
    can_acquire pair_primitive fork_primitive(platform:NamespaceQueueContract)cursor worlds ticks final final_worlds
    world before_world before_queues fork_queues owner child parent_program child_program child_memory child_run
    cgroup_binding report_binding channel capabilities_before after_capabilities queue_after start limit path arguments environment
    process_before_fork process_after_fork other process_after group mayTrace history namespace initial_group context,
  PairCapabilityContract pair_primitive ->ForkCapabilityContract fork_primitive ->
  NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
  CapabilityBirth operation groups runs native metadata external can_acquire owner child
    pair_primitive fork_primitive snapshot parent_program channel capabilities_before ->
  CapabilityHistory operation groups runs native metadata external can_acquire owner child capabilities_before ticks after_capabilities ->
  SourceProgramOwner runs owner parent_program ->nth_error runs parent_program=Some run ->
  SourceProgramOwner runs child child_program ->nth_error runs child_program=Some child_run ->
  cursor parent_program=S(length(source_fork_common _ _ fork)) ->cursor child_program=0%nat ->
  worlds parent_program=world ->worlds child_program=namespace_fork_child world snapshot ->
  namespace_queue_steps platform before_world before_queues(source_fork_common _ _ fork)world fork_queues ->
  fork_matches world snapshot ->fork_parent snapshot=physical_identity_task owner ->fork_child snapshot=physical_identity_task child ->
  fork_inherited_table snapshot first=Some(endpoint_binding channel parent_endpoint) ->
  NativeForkCopy(source_cell run)(source_fork_before _ _ fork)(source_fork_parent _ _ fork)child_memory ->
  Lean.eq(argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight borrowed)))
    (argument_bytes(map Byte.repr[114;117;110])) ->
  namespace_table before_world cgroup=Some cgroup_binding ->namespace_table before_world report=Some report_binding ->
  source_cell child_run=source_cell run ->
  source_before child_run=live(Returnstate(Vint Int.zero)(source_fork_continuation _ _ fork)child_memory) ->
  In(namespace_guest_event(entry_image path arguments environment))(source_events child_run) ->
  (forall offset tick,nth_error ticks offset=Some tick ->SourceIO runs tick) ->
  (forall offset tick,nth_error ticks offset=Some tick ->LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick) ->
  physical_queue_execution channel(fork_queues channel)ticks queue_after ->
  SourceOtherContract other groups(physical_identity_task owner)(physical_identity_task child) ->
  SourceProcessSchedule operation groups child runs parent_program other cursor worlds process_after_fork ticks final final_worlds process_after ->
  ForkProcessEffect(worlds parent_program)process_before_fork snapshot process_after_fork ->
  namespace_sigchld(worlds parent_program)=default_signal_action ->
  process_sole_waiter process_before_fork(fork_parent snapshot)=true ->
  SourceFileView groups process_after_fork(physical_identity_task owner)(worlds parent_program) ->
  process_cgroup_files process_after_fork(physical_identity_task owner)cgroup=Some group ->
  PreparedCgroupHandles groups(namespace_table(worlds parent_program))cgroup ->
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child history
    (LeanCage_Entry_CallerPhysical_born namespace initial_group)(tick_values ticks)context ->
  (forall offset tick,nth_error ticks offset=Some tick ->PlacementRecording groups tick) ->
  (forall offset tick,nth_error ticks offset=Some tick ->forall actor,
    unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)) ->
    forall object assigned,groups object=Some assigned ->
      object_absent(physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)))(ordinary_object object)) ->
  inhabited(SourceScopeProduction owner child start limit ticks group failure channel groups).
Proof.
  intros ROOT TLS BLOCKS CG_VALID PF_VALID CG_TLS CG_LOAD INPUT PERMISSIONS ERROR IN OUT ERR
    PARENT REPORT SEQUENCE CG_IN CG_OUT CG_ERR CG_PARENT.
  destruct(actual_prepared_recorded_fork_from_raw run snapshot fork before prepared borrowed input output errors le parentfd report cgroup sequence
    ROOT TLS BLOCKS CG_VALID PF_VALID CG_TLS CG_LOAD INPUT PERMISSIONS ERROR IN OUT ERR PARENT REPORT SEQUENCE
    CG_IN CG_OUT CG_ERR CG_PARENT)as[scope[first[second[failure[reply[parent PROPERTIES]]]]]].
  destruct PROPERTIES as[CELL PROPERTIES]. destruct PROPERTIES as[BORROWED PROPERTIES].
  destruct PROPERTIES as[STDIN PROPERTIES]. destruct PROPERTIES as[STDOUT PROPERTIES].
  destruct PROPERTIES as[STDERR PROPERTIES]. destruct PROPERTIES as[HISTORY PROPERTIES].
  destruct PROPERTIES as[CONTINUATION PROPERTIES]. destruct PROPERTIES as[ENV PROPERTIES].
  destruct PROPERTIES as[TEMPS PROPERTIES]. destruct PROPERTIES as[PARENT_FD PROPERTIES].
  destruct PROPERTIES as[REPORT_FD PROPERTIES]. destruct PROPERTIES as[CGROUP_FD PROPERTIES].
  destruct PROPERTIES as[SEQ PROPERTIES]. destruct PROPERTIES as[[child_temps[CONT[LOG FRONTIER]]] ADMISSION].
  exists first,failure;split.
  { exists scope,second,reply,child_temps;repeat split;assumption. }
  intros operation linux groups runs native metadata external can_acquire pair_primitive fork_primitive platform cursor worlds ticks
    final final_worlds world before_world before_queues fork_queues owner child parent_program child_program child_memory child_run
    cgroup_binding report_binding channel capabilities_before after_capabilities queue_after start limit path arguments environment
    process_before_fork process_after_fork other process_after group mayTrace history namespace initial_group context
    PAIR FORK NATIVE METADATA BIRTH CAPABILITIES PARENT_OWNER PARENT_PROGRAM CHILD_OWNER CHILD_PROGRAM PARENT_CURSOR CHILD_CURSOR
    PARENT_WORLD CHILD_WORLD QUEUES MATCH PARENT_ID CHILD_ID PEER COPY MODE CGROUP REPORTING CHILD_CELL CHILD_START IMAGE IO ORIGINS QUEUE
    OTHER PROCESS FORK_PROCESS DEFAULT SOLE FILES FILE HANDLES JOURNAL PLACEMENTS FOREIGN.
  constructor;constructor.
  eapply(actual_fork_source_scope_producer operation linux groups runs native metadata external can_acquire pair_primitive fork_primitive
    platform cursor worlds ticks final final_worlds scope first second failure reply world before_world before_queues fork_queues snapshot
    owner child parent_program child_program run fork child_memory parent child_run prepared cgroup_binding report_binding channel
    capabilities_before after_capabilities queue_after start limit path arguments environment child_temps process_before_fork process_after_fork
    other process_after group mayTrace history namespace initial_group context);try eassumption.
  - symmetry;exact CELL.
  - rewrite ENV,TEMPS;exact ROOT.
  - rewrite CELL;exact COPY.
  - rewrite BORROWED;exact MODE.
  - rewrite CGROUP_FD;exact CGROUP.
  - rewrite REPORT_FD;exact REPORTING.
  - rewrite CELL;exact CHILD_CELL.
  - rewrite CGROUP_FD;exact FILE.
  - rewrite CGROUP_FD;exact HANDLES.
Qed.
