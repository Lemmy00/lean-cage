(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Preserve one actual prepared caller and both source branches. *)
From Stdlib Require Import ZArith List Lia FunctionalExtensionality.
From compcert Require Import Coqlib Maps AST Integers Values Memory Clight.
From LeanImport Require Import Lean.
Require Import Machine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffAllocation NativeHandoffArguments
  NativeHandoffInput NativeHandoffInputWitness.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessSourceWorlds ProcessSourceTables ProcessLaunchWitness ProcessLaunchRecordingWitness
  ProcessParentRecordingWitness ProcessChildRecordingWitness ProcessChildTickWitness ProcessChildOtherWitness
  ProcessWorkerOtherWitness ProcessCapabilityRecording ProcessCapabilityBirth ProcessPreparationWitness
  ProcessEntryWitness ProcessEntryComposition ProcessPrimitiveWitness ProcessPrimitiveRuns ProcessPrimitiveData ProcessPrimitiveHistory
  ProcessPrimitivePrefix ProcessPrimitiveWorlds ProcessSourceOrigin ProcessEntryQueue ProcessEntryObservationsRuntime
  ProcessEntryObservations ProcessNativeCapabilities ProcessCallerConnection ProcessScopeRecording ProcessEntryTickBridge.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespacePaths NamespaceKernel NamespacePhysical
  NamespaceFork NamespaceForkWitness NamespaceForkWorldWitness NamespaceGuestFlags NamespaceWitnessConnection
  NamespaceSourceFork NamespaceCapabilities NamespaceQueue NamespaceChannel NamespaceDescriptorOrigin NamespaceScopeFactory
  NamespaceCaller NamespaceMemory NamespacePrepared NamespaceParentInput NamespaceLaunchWorldWitness NamespaceCgroupAuthority.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Record ActualEntrySources(namespace_id:nat):Type:={
  entry_source_parent:CallerSourceRun;
  entry_source_child:CallerSourceRun;
  entry_source_fork:ActualSourceFork entry_source_parent(Int.repr 2);
  entry_source_pair:block;
  entry_source_parent_events:list process_event;
  entry_source_child_events:list process_event;
  entry_source_parent_ticks:list LeanCage_Entry_CallerPhysical_Tick;
  entry_source_child_ticks:list LeanCage_Entry_CallerPhysical_Tick;
  entry_source_parent_namespace:NamespaceWorld;
  entry_source_child_namespace:NamespaceWorld;
  entry_source_image_locals:HandoffLocals;
  entry_source_image_memory:mem;
  entry_source_image_world:NamespaceWorld;
  entry_source_parent_actor:source_actor entry_source_parent=launch_recording_owner;
  entry_source_child_actor:source_actor entry_source_child=launch_recording_child;
  entry_source_parent_program:SourceProgramOwner[entry_source_parent;entry_source_child]launch_recording_owner 0;
  entry_source_child_program:SourceProgramOwner[entry_source_parent;entry_source_child]launch_recording_child 1;
  entry_source_common:source_fork_common _ _ entry_source_fork=
    repeat namespace_source_event 4++namespace_child_common_log entry_source_pair(Int.repr 9)(Int.repr 10);
  entry_source_parent_body:source_fork_body _ _ entry_source_fork=map namespace_process entry_source_parent_events;
  entry_source_child_body:source_events entry_source_child=map namespace_process entry_source_child_events;
  entry_source_child_start:source_before entry_source_child=live(Returnstate(Vint Int.zero)
    (source_fork_continuation _ _ entry_source_fork)(source_fork_before _ _ entry_source_fork));
  entry_source_child_finish:source_after entry_source_child=dead entry_source_image_memory;
  entry_source_copy:NativeForkCopy(source_cell entry_source_parent)(source_fork_before _ _ entry_source_fork)
    (source_fork_parent _ _ entry_source_fork)(source_fork_before _ _ entry_source_fork);
  entry_source_parent_recording:ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world
    entry_stopped_process entry_source_parent_events entry_source_parent_ticks entry_source_parent_namespace entry_admitted_process;
  entry_source_child_recording:ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0
    child_fork_namespace entry_fork_process entry_source_child_events entry_source_child_ticks entry_source_child_namespace entry_worker_process;
  entry_source_child_table:namespace_table entry_source_child_namespace=fork_fixture_worker_table;
  entry_source_native_input:namespace_worker_ordinary_input entry_source_image_locals entry_source_image_memory entry_source_image_world;
  entry_source_image_table:namespace_table entry_source_image_world=namespace_table entry_source_child_namespace;
  entry_source_child_quiet:Forall(fun event=>NamespaceSocket.namespace_socket_io event=None)(source_events entry_source_child);
  entry_source_prepared:UsefulPreparedSource entry_source_parent entry_source_fork entry_source_pair;
  entry_source_cells:source_cell entry_source_child=source_cell entry_source_parent;
  entry_source_actual_image:In(namespace_guest_event(entry_image
    (Vptr(NativeHandoffArguments.handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
    (Vptr(handoff_arguments entry_source_image_locals)Ptrofs.zero)
    (Vptr(handoff_environment entry_source_image_locals)Ptrofs.zero)))(source_events entry_source_child);
  entry_source_birth:forall native metadata external can_acquire,
    CapabilityBirth launch_operation launch_group_objects[entry_source_parent;entry_source_child]native metadata external can_acquire
      launch_recording_owner launch_recording_child pair_capability_model fork_capability_model fork_fixture_snapshot
      0 60 launch_fork_capabilities
}.

Arguments entry_source_parent {namespace_id} _.
Arguments entry_source_child {namespace_id} _.
Arguments entry_source_fork {namespace_id} _.
Arguments entry_source_pair {namespace_id} _.
Arguments entry_source_parent_events {namespace_id} _.
Arguments entry_source_child_events {namespace_id} _.
Arguments entry_source_parent_ticks {namespace_id} _.
Arguments entry_source_child_ticks {namespace_id} _.
Arguments entry_source_parent_namespace {namespace_id} _.
Arguments entry_source_child_namespace {namespace_id} _.
Arguments entry_source_image_locals {namespace_id} _.
Arguments entry_source_image_memory {namespace_id} _.
Arguments entry_source_image_world {namespace_id} _.
Arguments entry_source_parent_actor {namespace_id} _.
Arguments entry_source_child_actor {namespace_id} _.
Arguments entry_source_parent_program {namespace_id} _.
Arguments entry_source_child_program {namespace_id} _.
Arguments entry_source_common {namespace_id} _.
Arguments entry_source_parent_body {namespace_id} _.
Arguments entry_source_child_body {namespace_id} _.
Arguments entry_source_child_start {namespace_id} _.
Arguments entry_source_child_finish {namespace_id} _.
Arguments entry_source_copy {namespace_id} _.
Arguments entry_source_parent_recording {namespace_id} _.
Arguments entry_source_child_recording {namespace_id} _.
Arguments entry_source_child_table {namespace_id} _.
Arguments entry_source_native_input {namespace_id} _.
Arguments entry_source_image_table {namespace_id} _.
Arguments entry_source_child_quiet {namespace_id} _.
Arguments entry_source_prepared {namespace_id} _.
Arguments entry_source_cells {namespace_id} _.
Arguments entry_source_actual_image {namespace_id} _.
Arguments entry_source_birth {namespace_id} _.

Theorem actual_entry_sources namespace_id:inhabited(ActualEntrySources namespace_id).
Proof.
  destruct(actual_useful_source_recording_chain namespace_id)
    as(parent &child &fork &pair &parent_events &child_events &parent_ticks &child_ticks &parent_namespace &child_namespace
      &b &image_memory &image_world &PARENT &CHILD &PARENT_OWNER &CHILD_OWNER &COMMON &PARENT_BODY &CHILD_BODY &CHILD_START &CHILD_END
      &COPY &PARENT_RECORDING &CHILD_RECORDING &CHILD_TABLE &INPUT &IMAGE_TABLE &QUIET &PREPARED &CELLS &IMAGE &BIRTH).
  constructor;refine{|entry_source_parent:=parent;entry_source_child:=child;entry_source_fork:=fork;entry_source_pair:=pair;
    entry_source_parent_events:=parent_events;entry_source_child_events:=child_events;entry_source_parent_ticks:=parent_ticks;
    entry_source_child_ticks:=child_ticks;entry_source_parent_namespace:=parent_namespace;entry_source_child_namespace:=child_namespace;
    entry_source_image_locals:=b;entry_source_image_memory:=image_memory;entry_source_image_world:=image_world|};assumption.
Qed.

Definition entry_common_labels {namespace_id}(source:ActualEntrySources namespace_id):=
  caller_lineage_values(source_fork_common _ _ (entry_source_fork source)).
Definition entry_child_labels {namespace_id}(source:ActualEntrySources namespace_id):=
  caller_lineage_values(source_events(entry_source_child source)).

Theorem entry_common_labels_checked namespace_id(source:ActualEntrySources namespace_id):
  LeanCage_Entry_CallerLabelsAllowed(entry_common_labels source).
Proof.
  eapply caller_source_labels_ordinary_Lean;[exact(source_started(entry_source_parent source))|].
  exact(source_fork_prefix _ _ (entry_source_fork source)).
Qed.

Theorem entry_child_labels_checked namespace_id(source:ActualEntrySources namespace_id):
  LeanCage_Entry_CallerLabelsAllowed(entry_child_labels source).
Proof.
  eapply caller_source_labels_ordinary_Lean;
    [exact(source_started(entry_source_child source))|exact(source_executed(entry_source_child source))].
Qed.

Definition entry_prefix_tables(source:ActualEntrySources 1):=
  launch_child_tables(entry_source_child_namespace source)(namespace_table fork_fixture_world).
Definition entry_tail_tables(source:ActualEntrySources 1):=
  launch_parent_tables(entry_source_parent_namespace source)fork_fixture_worker_table.
Definition entry_complete_ticks(source:ActualEntrySources 1):=
  entry_runtime_ticks(entry_source_child_ticks source)(entry_source_parent_ticks source)(entry_prefix_tables source)(entry_tail_tables source).
Definition entry_complete_native(source:ActualEntrySources 1):=
  entry_runtime_native(entry_source_child_ticks source)(entry_source_parent_ticks source)(entry_prefix_tables source)(entry_tail_tables source)
    (fun _ _=>Logic.True).
Definition entry_complete_metadata(source:ActualEntrySources 1):=
  entry_runtime_metadata(entry_source_child_ticks source)(entry_source_parent_ticks source)(entry_prefix_tables source)(entry_tail_tables source)
    (fun _ _=>Logic.True).
Definition entry_complete_external:CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityAction->CapabilityWorld->Prop:=
  fun _ _ _ _=>Logic.False.
Definition entry_complete_context:=primitive_context true task_running(Int64.repr 1048592)(Some 1).
Definition entry_complete_capabilities(source:ActualEntrySources 1):=
  entry_primitive_capabilities(entry_tail_tables source)(primitive_snapshot_table 7).

Theorem entry_complete_recorded(source:ActualEntrySources 1):
  inhabited(EntryRecordedComposition 1(entry_source_parent source)(entry_source_child source)(entry_source_fork source)
    (entry_source_pair source)(entry_source_parent_events source)(entry_source_child_events source)
    (entry_source_parent_namespace source)(entry_source_child_namespace source)(entry_complete_ticks source)entry_admitted_process
    (entry_complete_native source)(entry_complete_metadata source)entry_complete_external(fun _ _=>Logic.True)
    (entry_complete_capabilities source)(fun _=>ProcessImport.True)entry_complete_context).
Proof.
  assert(PREFIX_VALID:forall actor,launch_nonnegative_table(entry_prefix_tables source actor)).
  { apply entry_primitive_child_tables_nonnegative;exact(entry_source_child_table source). }
  assert(TAIL_VALID:forall actor,launch_nonnegative_table(entry_tail_tables source actor)).
  { eapply entry_primitive_parent_tables_nonnegative;[exact(entry_source_parent_recording source)|exact launch_actual_fork_nonnegative]. }
  pose proof(entry_worker_prefix_capabilities(entry_source_child_ticks source)(entry_source_parent_ticks source)
    (entry_prefix_tables source)(entry_tail_tables source)(fun _ _=>Logic.True)entry_complete_external
    [entry_source_parent source;entry_source_child source]PREFIX_VALID)as PREFIX.
  unfold entry_prefix_tables in PREFIX;rewrite(entry_primitive_child_world _ _ (entry_source_child_table source))in PREFIX.
  rewrite(entry_child_capabilities_are_parent _ (entry_source_child_table source))in PREFIX.
  pose proof(entry_worker_tail_capabilities(entry_source_child_ticks source)(entry_source_parent_ticks source)
    (entry_prefix_tables source)(entry_tail_tables source)(fun _ _=>Logic.True)entry_complete_external
    [entry_source_parent source;entry_source_child source]TAIL_VALID)as TAIL.
  unfold entry_tail_tables in TAIL;rewrite entry_primitive_parent_world in TAIL.
  eapply(entry_actual_recorded_composition 1(entry_source_parent source)(entry_source_child source)(entry_source_fork source)
    (entry_source_pair source)(entry_source_parent_events source)(entry_source_child_events source)(entry_source_parent_ticks source)
    (entry_source_child_ticks source)(entry_source_parent_namespace source)(entry_source_child_namespace source)
    (entry_worker_prefix(entry_prefix_tables source))(entry_worker_tail(entry_tail_tables source))entry_admitted_process
    (entry_complete_native source)(entry_complete_metadata source)entry_complete_external(fun _ _=>Logic.True)
    (entry_complete_capabilities source)(fun _=>ProcessImport.True)entry_complete_context).
  - exact(entry_source_parent_actor source).
  - exact(entry_source_child_actor source).
  - exact(entry_source_common source).
  - exact(entry_source_parent_body source).
  - exact(entry_source_child_body source).
  - exact(entry_source_child_table source).
  - exact(entry_source_child_quiet source).
  - exact(entry_source_prepared source).
  - exact(entry_source_parent_recording source).
  - exact(entry_source_child_recording source).
  - apply(entry_source_birth source).
  - apply entry_worker_prefix_process.
  - apply entry_worker_tail_process.
  - exact PREFIX.
  - exact TAIL.
  - apply entry_worker_prefix_recorded.
  - apply entry_worker_tail_recorded.
Qed.

Theorem entry_complete_io(source:ActualEntrySources 1):
  inhabited(EntryIORecording[entry_source_parent source;entry_source_child source]launch_recording_owner launch_recording_child
    (entry_complete_ticks source)).
Proof.
  eapply(entry_concrete_io_recording (entry_source_parent source)(entry_source_child source)(entry_source_fork source)
    (entry_source_pair source)(entry_source_parent_events source)(entry_source_child_events source)(entry_source_parent_ticks source)
    (entry_source_child_ticks source)(entry_source_parent_namespace source)(entry_source_child_namespace source)
    (entry_prefix_tables source)(entry_tail_tables source)).
  - exact(entry_source_parent_actor source).
  - exact(entry_source_child_actor source).
  - exact(entry_source_common source).
  - exact(entry_source_parent_body source).
  - exact(entry_source_child_body source).
  - exact(entry_source_parent_recording source).
  - exact(entry_source_child_recording source).
Qed.

Theorem entry_complete_queue(source:ActualEntrySources 1):
  physical_queue_execution 60 channel_empty(entry_complete_ticks source)channel_empty.
Proof.
  eapply(actual_prepared_recorded_entry_queue 1(entry_source_parent source)(entry_source_child source)(entry_source_fork source)
    (entry_source_pair source)(entry_source_parent_events source)(entry_source_child_events source)(entry_source_parent_ticks source)
    (entry_source_child_ticks source)(entry_source_parent_namespace source)(entry_source_child_namespace source)
    (entry_prefix_tables source)(entry_tail_tables source)).
  - exact(entry_source_prepared source).
  - exact(entry_source_parent_body source).
  - exact(entry_source_child_body source).
  - exact(entry_source_child_quiet source).
  - exact(entry_source_parent_recording source).
  - exact(entry_source_child_recording source).
Qed.

Theorem entry_complete_placements(source:ActualEntrySources 1):
  Forall(PlacementRecording launch_group_objects)(entry_complete_ticks source).
Proof.
  eapply entry_complete_placement_recordings;
    [exact(entry_source_parent_recording source)|exact(entry_source_child_recording source)].
Qed.

Lemma entry_prefix_foreign_tables(source:ActualEntrySources 1)actor:
  actor<>1 ->actor<>2 ->entry_prefix_tables source actor=entry_foreign_tables actor.
Proof.
  intros NOT_PARENT NOT_CHILD;unfold entry_prefix_tables,launch_child_tables,entry_foreign_tables.
  assert(PARENT:Nat.eqb actor 1=false)by(apply Nat.eqb_neq;exact NOT_PARENT).
  assert(CHILD:Nat.eqb actor 2=false)by(apply Nat.eqb_neq;exact NOT_CHILD).
  rewrite PARENT,CHILD;reflexivity.
Qed.

Lemma entry_tail_foreign_tables(source:ActualEntrySources 1)actor:
  actor<>1 ->actor<>2 ->entry_tail_tables source actor=entry_foreign_tables actor.
Proof.
  intros NOT_PARENT NOT_CHILD;unfold entry_tail_tables,launch_parent_tables,entry_foreign_tables.
  assert(PARENT:Nat.eqb actor 1=false)by(apply Nat.eqb_neq;exact NOT_PARENT).
  assert(CHILD:Nat.eqb actor 2=false)by(apply Nat.eqb_neq;exact NOT_CHILD).
  rewrite PARENT,CHILD;reflexivity.
Qed.

Theorem entry_complete_foreign(source:ActualEntrySources 1):Forall EntryForeignCgroupAbsent(entry_complete_ticks source).
Proof.
  eapply entry_complete_foreign_cgroup_observations.
  - exact(entry_source_parent_recording source).
  - exact(entry_source_child_recording source).
  - apply entry_primitive_child_tables_nonnegative;exact(entry_source_child_table source).
  - exact(entry_prefix_foreign_tables source).
  - eapply entry_primitive_parent_tables_nonnegative;
      [exact(entry_source_parent_recording source)|exact launch_actual_fork_nonnegative].
  - exact(entry_tail_foreign_tables source).
Qed.

Lemma entry_initial_cgroup_handles:
  PreparedCgroupHandles launch_group_objects(namespace_table fork_fixture_world)(Int.repr 7).
Proof.
  intros object group CLASS;unfold launch_group_objects in CLASS.
  destruct(Nat.eqb object 103)eqn:SELECTED;[|discriminate].
  apply Nat.eqb_eq in SELECTED;subst object;exact launch_fork_cgroup_unique.
Qed.

Lemma entry_initial_file_view:
  SourceFileView launch_group_objects entry_fork_process(physical_identity_task launch_recording_owner)fork_fixture_world.
Proof.
  rewrite launch_recording_owner_task;intros fd group.
  change(launch_fork_files physical_parent fd=Some group <->exists binding object,
    namespace_table fork_fixture_world fd=Some binding /\descriptor_object binding=ordinary_object object /\
    launch_group_objects object=Some group).
  assert(FILES:launch_fork_files physical_parent fd=launch_parent_files physical_parent fd).
  { unfold launch_fork_files,launch_parent_files;rewrite launch_task_eq_same;reflexivity. }
  rewrite FILES;exact(launch_actual_fork_file_view fd group).
Qed.

Definition entry_exec_offset(source:ActualEntrySources 1):=
  length(entry_source_child_ticks source)+74+length(entry_source_parent_ticks source)+68.

Definition entry_ordinary_ticks(source:ActualEntrySources 1):=
  LeanCage_Entry_CallerWitness_usefulEntryTicks launch_recording_owner launch_recording_child
    (entry_primitive_other_objects(entry_prefix_tables source))(entry_primitive_other_objects(entry_tail_tables source))
    (entry_primitive_other_flags(entry_prefix_tables source))(entry_primitive_other_flags(entry_tail_tables source))
    (tick_values(entry_source_child_ticks source))(tick_values(entry_source_parent_ticks source))entry_complete_context.

Theorem entry_complete_scope(source:ActualEntrySources 1):
  inhabited(SourceScopeProduction launch_recording_owner launch_recording_child 0(Nat_of_nat(entry_exec_offset source))
    (entry_complete_ticks source)1(Int.repr 60)60 launch_group_objects).
Proof.
  destruct(entry_complete_recorded source)as[recorded].
  destruct(entry_complete_io source)as[io].
  destruct(entry_source_prepared source)
    as(initial &cell &command &input_source &before &e &memory &parameters &finished &request
      &INITIAL &CELL &START &CANONICAL &INPUT &PREPARED &CONT &PARENT_MEMORY &FINISHED &SHAPE).
  destruct(namespace_useful_preparation_raw _ _ _ _ _ _ _ INPUT PREPARED)
    as[TLS[BLOCKS[CG_VALID[PF_VALID[CG_TLS[CG_LOAD[BORROWED PERMISSIONS]]]]]]].
  destruct namespace_useful_prepared_scalars as[ERROR[IN[OUT[ERR[PARENT[REPORT SEQUENCE]]]]]].
  assert(ROOT:source_before(entry_source_parent source)=live(State f_namespace_init(namespace_tail 9)Kstop
    (namespace_initial_env before)namespace_useful_parent_temps memory))by(rewrite <-CANONICAL;exact START).
  pose proof(actual_prepared_source_scope_from_raw(entry_source_parent source)fork_fixture_snapshot(entry_source_fork source)
    before memory(handoff_fixture_input command input_source)(Int.repr 4)(Int.repr 5)(Int.repr 6)namespace_useful_parent_temps
    (Int.repr 3)(Int.repr 8)(Int.repr 7)Int64.zero ROOT
    ltac:(rewrite CELL;exact TLS)BLOCKS CG_VALID PF_VALID ltac:(rewrite CELL;exact CG_TLS)CG_LOAD
    ltac:(rewrite CELL;exact BORROWED)PERMISSIONS ERROR IN OUT ERR PARENT REPORT SEQUENCE
    ltac:(vm_compute;discriminate)ltac:(vm_compute;discriminate)ltac:(vm_compute;discriminate)ltac:(vm_compute;discriminate))as RAW.
  destruct RAW as[first[failure[ORIGIN PRODUCE]]].
  destruct(actual_useful_descriptor_origin _ _ _ (entry_source_pair source)first failure(entry_source_common source)ORIGIN)
    as[FIRST FAILURE];subst first failure.
  eapply(PRODUCE launch_operation launch_linux_contract launch_group_objects[entry_source_parent source;entry_source_child source]
    (entry_complete_native source)(entry_complete_metadata source)entry_complete_external(fun _ _=>Logic.True)
    pair_capability_model fork_capability_model namespace_queue_model entry_initial_cursor entry_initial_worlds(entry_complete_ticks source)
    (entry_composed_cursor recorded)(entry_composed_worlds recorded)fork_fixture_world fork_fixture_initial
    (fun _=>channel_empty)(fork_fixture_reset(fun _=>channel_empty))launch_recording_owner launch_recording_child 0 1
    (source_fork_before _ _ (entry_source_fork source))(entry_source_child source)
    {|descriptor_object:=ordinary_object 103;descriptor_cloexec:=true|}
    {|descriptor_object:=ordinary_object 104;descriptor_cloexec:=true|}
    60 launch_fork_capabilities(entry_complete_capabilities source)channel_empty 0(Nat_of_nat(entry_exec_offset source))
    (Vptr(NativeHandoffArguments.handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
    (Vptr(handoff_arguments(entry_source_image_locals source))Ptrofs.zero)
    (Vptr(handoff_environment(entry_source_image_locals source))Ptrofs.zero)
    launch_before_fork entry_fork_process(UsefulEntryOther launch_group_objects[entry_source_parent source;entry_source_child source])
    entry_admitted_process 1(fun _=>ProcessImport.True)
    (caller_request_values(source_runs_history[entry_source_parent source;entry_source_child source]))(Nat_of_nat 1)
    (ProcessImport.Option_none_inst1 Lean.Nat)entry_complete_context).
  - exact pair_capability_linux.
  - exact fork_capability_linux.
  - apply recorded_native_capability_contract.
  - apply recorded_metadata_capability_contract.
  - exact(entry_composed_birth recorded).
  - exact(entry_composed_capabilities recorded).
  - exact(entry_source_parent_program source).
  - reflexivity.
  - exact(entry_source_child_program source).
  - reflexivity.
  - change(61=S(length(source_fork_common(entry_source_parent source)(Int.repr 2)(entry_source_fork source)))).
    rewrite(entry_source_common source),preparation_common_length;reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - change(namespace_queue_steps namespace_queue_model fork_fixture_initial(fun _=>channel_empty)
      (source_fork_common(entry_source_parent source)(Int.repr 2)(entry_source_fork source))fork_fixture_world
      (fork_fixture_reset(fun _=>channel_empty))).
    rewrite(entry_source_common source);apply namespace_useful_phase9_queue.
  - exact(proj1 namespace_useful_common_fork).
  - rewrite launch_recording_owner_task;reflexivity.
  - rewrite launch_recording_child_task;reflexivity.
  - reflexivity.
  - exact(entry_source_copy source).
  - constructor.
  - reflexivity.
  - reflexivity.
  - exact(entry_source_cells source).
  - exact(entry_source_child_start source).
  - exact(entry_source_actual_image source).
  - exact(entry_recorded_io io).
  - exact(entry_recorded_origins io).
  - exact(entry_complete_queue source).
  - exact(entry_composed_other_contract recorded).
  - exact(entry_composed_processes recorded).
  - apply launch_same_fork_process;[exact(proj1 namespace_useful_common_fork)|reflexivity|reflexivity].
  - exact(proj1(proj2 namespace_useful_common_fork)).
  - reflexivity.
  - exact entry_initial_file_view.
  - rewrite launch_recording_owner_task;unfold entry_fork_process,launch_world;cbn[process_cgroup_files].
    unfold launch_fork_files;rewrite launch_task_eq_same;reflexivity.
  - exact entry_initial_cgroup_handles.
  - exact(entry_composed_journal recorded).
  - intros offset tick SELECTED;pose proof(entry_complete_placements source)as PLACED.
    rewrite Forall_forall in PLACED;apply PLACED;eapply nth_error_In;exact SELECTED.
  - intros offset tick SELECTED;pose proof(entry_complete_foreign source)as FOREIGN.
    rewrite Forall_forall in FOREIGN;apply FOREIGN;eapply nth_error_In;exact SELECTED.
Qed.

Theorem entry_complete_parent_slice(source:ActualEntrySources 1):
  LeanCage_Entry_CallerWitness_SupervisorSlice(fun _=>ProcessImport.True)launch_recording_owner launch_recording_child
    (tick_values(entry_complete_ticks source))(Nat_of_nat(length(entry_source_child_ticks source)+74))
    (primitive_context true task_running Int64.zero None)
    (Nat_of_nat(length(entry_source_child_ticks source)+74+length(entry_source_parent_ticks source)))entry_complete_context.
Proof.
  pose proof(parent_recording_supervisor_slice _ _ _ _ _ _ _ _ _ _ _(entry_source_parent_recording source)
    (fun _=>ProcessImport.True)
    (entry_source_child_ticks source++entry_worker_prefix(entry_prefix_tables source))
    (entry_worker_tail(entry_tail_tables source)))as SLICE.
  rewrite length_app,entry_worker_prefix_length in SLICE.
  repeat rewrite <-app_assoc in SLICE;exact SLICE.
Qed.

Record EntryAcceptance:Type:={
  acceptance_source:ActualEntrySources 1;
  acceptance_history:EntryRecordedComposition 1(entry_source_parent acceptance_source)(entry_source_child acceptance_source)
    (entry_source_fork acceptance_source)(entry_source_pair acceptance_source)(entry_source_parent_events acceptance_source)
    (entry_source_child_events acceptance_source)(entry_source_parent_namespace acceptance_source)(entry_source_child_namespace acceptance_source)
    (entry_complete_ticks acceptance_source)entry_admitted_process(entry_complete_native acceptance_source)
    (entry_complete_metadata acceptance_source)entry_complete_external(fun _ _=>Logic.True)(entry_complete_capabilities acceptance_source)
    (fun _=>ProcessImport.True)entry_complete_context;
  acceptance_io:EntryIORecording[entry_source_parent acceptance_source;entry_source_child acceptance_source]
    launch_recording_owner launch_recording_child(entry_complete_ticks acceptance_source);
  acceptance_queue:physical_queue_execution 60 channel_empty(entry_complete_ticks acceptance_source)channel_empty;
  acceptance_placements:Forall(PlacementRecording launch_group_objects)(entry_complete_ticks acceptance_source);
  acceptance_foreign:Forall EntryForeignCgroupAbsent(entry_complete_ticks acceptance_source);
  acceptance_scope:SourceScopeProduction launch_recording_owner launch_recording_child 0
    (Nat_of_nat(entry_exec_offset acceptance_source))(entry_complete_ticks acceptance_source)1(Int.repr 60)60 launch_group_objects;
  acceptance_parent_slice:LeanCage_Entry_CallerWitness_SupervisorSlice(fun _=>ProcessImport.True)
    launch_recording_owner launch_recording_child(tick_values(entry_complete_ticks acceptance_source))
    (Nat_of_nat(length(entry_source_child_ticks acceptance_source)+74))(primitive_context true task_running Int64.zero None)
    (Nat_of_nat(length(entry_source_child_ticks acceptance_source)+74+length(entry_source_parent_ticks acceptance_source)))entry_complete_context;
  acceptance_common_labels:LeanCage_Entry_CallerLabelsAllowed(entry_common_labels acceptance_source);
  acceptance_child_labels:LeanCage_Entry_CallerLabelsAllowed(entry_child_labels acceptance_source);
  acceptance_public_ticks:tick_values(entry_complete_ticks acceptance_source)=entry_ordinary_ticks acceptance_source
}.

Theorem actual_entry_acceptance:inhabited EntryAcceptance.
Proof.
  destruct(actual_entry_sources 1)as[source].
  destruct(entry_complete_recorded source)as[history].
  destruct(entry_complete_io source)as[io].
  destruct(entry_complete_scope source)as[scope].
  constructor;refine{|acceptance_source:=source;acceptance_history:=history;acceptance_io:=io;acceptance_scope:=scope|}.
  - exact(entry_complete_queue source).
  - exact(entry_complete_placements source).
  - exact(entry_complete_foreign source).
  - exact(entry_complete_parent_slice source).
  - exact(entry_common_labels_checked _ source).
  - exact(entry_child_labels_checked _ source).
  - apply entry_runtime_ticks_ordinary.
Qed.
