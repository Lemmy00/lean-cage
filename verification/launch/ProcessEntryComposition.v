(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Join the actual source branches and worker at identical process worlds. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds ProcessLaunchWitness ProcessLaunchRecordingWitness
  ProcessParentRecordingWitness ProcessChildRecordingWitness ProcessChildTickWitness ProcessChildOtherWitness
  ProcessWorkerOtherWitness ProcessParentCapabilityWitness ProcessCapabilityRecording ProcessRecordedComposition
  ProcessPreparationWitness ProcessEntryWitness ProcessCallerConnection ProcessCapabilityBirth
  ProcessPrimitiveWitness ProcessPrimitiveRuns.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceWorldTrace NamespacePhysical
  NamespaceForkWorldWitness NamespaceSourceFork NamespaceForkWitness NamespaceSocket NamespacePaths.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Definition entry_fork_process:=launch_world launch_fork_files None task_running Int64.zero None.
Definition entry_worker_process:=launch_world launch_parent_files None task_running Int64.zero None.
Definition entry_stopped_process:=launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None.
Definition entry_admitted_process:=
  launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1%nat).
Definition entry_initial_cursor(query:nat):=if Nat.eqb query 0 then 61%nat else 0%nat.
Definition entry_initial_worlds(query:nat):=if Nat.eqb query 1 then child_fork_namespace else fork_fixture_world.

Theorem entry_recording_process_schedule namespace_id parent child parent_prefix parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace worker_prefix worker_tail after:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_events parent=parent_prefix++map namespace_process parent_events ->length parent_prefix=61%nat ->
  source_events child=map namespace_process child_events ->
  Forall(fun event=>namespace_socket_io event=None)(source_events child) ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  UsefulWorkerRun entry_worker_process worker_prefix entry_stopped_process ->
  UsefulWorkerRun entry_admitted_process worker_tail after ->
  exists final final_worlds,
    SourceProcessSchedule launch_operation launch_group_objects launch_recording_child[parent;child]0
      (UsefulEntryOther launch_group_objects[parent;child])entry_initial_cursor entry_initial_worlds entry_fork_process
      (child_ticks++worker_prefix++parent_ticks++worker_tail)final final_worlds after /\
    final 0=(61+length parent_events)%nat /\final 1=length child_events /\
    final_worlds 0=parent_namespace /\final_worlds 1=child_namespace /\
    forall query,query<>0%nat ->query<>1%nat ->
      final query=entry_initial_cursor query /\final_worlds query=entry_initial_worlds query.
Proof.
  intros PARENT CHILD PARENT_EVENTS PARENT_LENGTH CHILD_EVENTS CHILD_QUIET PARENT_RECORDING CHILD_RECORDING PREFIX TAIL.
  assert(QUIET:Forall(fun event=>namespace_socket_io(namespace_process event)=None)child_events).
  { apply Forall_forall;intros event MEMBER;rewrite Forall_forall in CHILD_QUIET;apply CHILD_QUIET.
    rewrite CHILD_EVENTS;apply in_map;exact MEMBER. }
  assert(CHILD_DECOMPOSE:source_events child=[]++map namespace_process child_events++[])
    by(rewrite CHILD_EVENTS;cbn;rewrite app_nil_r;reflexivity).
  destruct(child_recording_other_schedule _ _ _ _ _ _ _ _ _ _ _ CHILD_RECORDING QUIET[parent;child]child[][]
    entry_initial_cursor entry_initial_worlds 0(UsefulEntryOther launch_group_objects[parent;child])
    (Logic.eq_refl _)CHILD CHILD_DECOMPOSE(Logic.eq_refl _)(Logic.eq_refl _)(Logic.eq_refl _)
    ltac:(discriminate)ltac:(intros;constructor;assumption))
    as[child_cursor[child_worlds[CHILD_RUN[CHILD_FINISH[CHILD_WORLD CHILD_FRAME]]]]].
  pose proof(useful_worker_process_schedule launch_group_objects[parent;child]0 child_cursor child_worlds
    entry_worker_process worker_prefix entry_stopped_process PREFIX)as PREFIX_RUN.
  assert(PARENT_CURSOR:child_cursor 0=61%nat).
  { destruct(CHILD_FRAME 0 ltac:(discriminate))as[POSITION TABLE];exact POSITION. }
  assert(PARENT_WORLD:child_worlds 0=fork_fixture_world).
  { destruct(CHILD_FRAME 0 ltac:(discriminate))as[POSITION TABLE];exact TABLE. }
  assert(PARENT_DECOMPOSE:source_events parent=parent_prefix++map namespace_process parent_events++[])
    by(rewrite PARENT_EVENTS,app_nil_r;reflexivity).
  destruct(owned_program_recording_processes _ _ _ _ _ _ _ _ _ _ _ _
    (parent_recording_owned _ _ _ _ _ _ _ _ _ _ _ PARENT_RECORDING)
    [parent;child]parent parent_prefix[]child_cursor child_worlds(UsefulEntryOther launch_group_objects[parent;child])
    (Logic.eq_refl _)PARENT PARENT_DECOMPOSE PARENT_LENGTH PARENT_CURSOR PARENT_WORLD)
    as[final[final_worlds[PARENT_RUN[PARENT_FINISH[PARENT_FINAL PARENT_FRAME]]]]].
  pose proof(useful_worker_process_schedule launch_group_objects[parent;child]0 final final_worlds
    entry_admitted_process worker_tail after TAIL)as TAIL_RUN.
  exists final,final_worlds;split.
  - eapply source_process_schedule_append;[exact CHILD_RUN|].
    eapply source_process_schedule_append;[exact PREFIX_RUN|].
    eapply source_process_schedule_append;[exact PARENT_RUN|exact TAIL_RUN].
  - split;[exact PARENT_FINISH|].
    destruct(PARENT_FRAME 1 ltac:(discriminate))as[FINAL_CHILD WORLD_CHILD].
    split;[rewrite FINAL_CHILD,CHILD_FINISH;reflexivity|].
    split;[exact PARENT_FINAL|]. split;[rewrite WORLD_CHILD;exact CHILD_WORLD|].
    intros query NOT_PARENT NOT_CHILD;destruct(PARENT_FRAME query NOT_PARENT)as[POSITION TABLE].
    destruct(CHILD_FRAME query NOT_CHILD)as[OLD_POSITION OLD_TABLE];split;congruence.
Qed.

Lemma entry_child_final_nonnegative groups program namespace_id parent ordinal namespace world events ticks after_namespace after_world:
  ChildRecording groups program namespace_id parent ordinal namespace world events ticks after_namespace after_world ->
  launch_nonnegative_table(namespace_table namespace) ->launch_nonnegative_table(namespace_table after_namespace).
Proof.
  intro RUN;induction RUN;intro VALID;[exact VALID|].
  apply IHRUN;eapply launch_namespace_nonnegative;[|exact VALID].
  exact(source_primitive_namespace _ _ _ _ _ _ _ H).
Qed.

Theorem entry_recording_capability_history namespace_id parent child parent_prefix parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace worker_prefix worker_tail native metadata external can_acquire after_capabilities:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_events parent=parent_prefix++map namespace_process parent_events ->length parent_prefix=61%nat ->
  source_events child=map namespace_process child_events ->namespace_table child_namespace=fork_fixture_worker_table ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child(parent_recording_capabilities fork_fixture_worker_table fork_fixture_world)
    worker_prefix(parent_recording_capabilities fork_fixture_worker_table fork_fixture_world) ->
  CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child(parent_recording_capabilities fork_fixture_worker_table parent_namespace)
    worker_tail after_capabilities ->
  CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child launch_fork_capabilities
    (child_ticks++worker_prefix++parent_ticks++worker_tail)after_capabilities.
Proof.
  intros PARENT CHILD PARENT_EVENTS PARENT_LENGTH CHILD_EVENTS CHILD_TABLE PARENT_RECORDING CHILD_RECORDING PREFIX TAIL.
  assert(CHILD_DECOMPOSE:source_events child=[]++map namespace_process child_events++[])
    by(rewrite CHILD_EVENTS;cbn;rewrite app_nil_r;reflexivity).
  pose proof(child_recording_capability_history _ _ _ _ _ _ _ _ _ _ _ CHILD_RECORDING launch_actual_fork_nonnegative
    [parent;child]child[][]native metadata external can_acquire(Logic.eq_refl _)CHILD CHILD_DECOMPOSE(Logic.eq_refl _))as CHILD_RUN.
  rewrite(entry_child_capabilities_are_parent child_namespace CHILD_TABLE),<-entry_fork_capabilities_are_child in CHILD_RUN.
  assert(WORKER_VALID:launch_nonnegative_table fork_fixture_worker_table).
  { rewrite <-CHILD_TABLE;eapply entry_child_final_nonnegative;[exact CHILD_RECORDING|exact launch_actual_fork_nonnegative]. }
  assert(PARENT_DECOMPOSE:source_events parent=parent_prefix++map namespace_process parent_events++[])
    by(rewrite PARENT_EVENTS,app_nil_r;reflexivity).
  pose proof(parent_recording_capability_history _ _ _ _ _ _ _ _ _ _ _ PARENT_RECORDING WORKER_VALID
    [parent;child]parent parent_prefix[]native metadata external can_acquire(Logic.eq_refl _)PARENT PARENT_DECOMPOSE PARENT_LENGTH)as PARENT_RUN.
  eapply capability_history_append;[exact CHILD_RUN|].
  eapply capability_history_append;[exact PREFIX|].
  eapply capability_history_append;[exact PARENT_RUN|exact TAIL].
Qed.

Theorem entry_actual_capability_history namespace_id parent child(fork:ActualSourceFork parent(Int.repr 2))pair
    parent_events child_events parent_ticks child_ticks parent_namespace child_namespace worker_prefix worker_tail
    native metadata external can_acquire after_capabilities:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_fork_common _ _ fork=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10) ->
  source_fork_body _ _ fork=map namespace_process parent_events ->
  source_events child=map namespace_process child_events ->namespace_table child_namespace=fork_fixture_worker_table ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child(parent_recording_capabilities fork_fixture_worker_table fork_fixture_world)
    worker_prefix(parent_recording_capabilities fork_fixture_worker_table fork_fixture_world) ->
  CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child(parent_recording_capabilities fork_fixture_worker_table parent_namespace)
    worker_tail after_capabilities ->
  CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child launch_fork_capabilities
    (child_ticks++worker_prefix++parent_ticks++worker_tail)after_capabilities.
Proof.
  intros PARENT CHILD COMMON BODY CHILD_EVENTS TABLE PARENT_RECORDING CHILD_RECORDING PREFIX TAIL.
  eapply(entry_recording_capability_history namespace_id parent child
    (source_fork_common _ _ fork++[namespace_forked(Int.repr 2)])parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace worker_prefix worker_tail native metadata external can_acquire after_capabilities);try eassumption.
  - rewrite(source_fork_events _ _ fork),BODY;rewrite <-app_assoc;reflexivity.
  - rewrite length_app,COMMON,preparation_common_length;reflexivity.
Qed.

Theorem entry_actual_process_schedule namespace_id parent child(fork:ActualSourceFork parent(Int.repr 2))pair
    parent_events child_events parent_ticks child_ticks parent_namespace child_namespace worker_prefix worker_tail after:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_fork_common _ _ fork=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10) ->
  source_fork_body _ _ fork=map namespace_process parent_events ->
  source_events child=map namespace_process child_events ->
  Forall(fun event=>namespace_socket_io event=None)(source_events child) ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  UsefulWorkerRun entry_worker_process worker_prefix entry_stopped_process ->
  UsefulWorkerRun entry_admitted_process worker_tail after ->
  exists final final_worlds,
    SourceProcessSchedule launch_operation launch_group_objects launch_recording_child[parent;child]0
      (UsefulEntryOther launch_group_objects[parent;child])entry_initial_cursor entry_initial_worlds entry_fork_process
      (child_ticks++worker_prefix++parent_ticks++worker_tail)final final_worlds after /\
    final 0=(61+length parent_events)%nat /\final 1=length child_events /\
    final_worlds 0=parent_namespace /\final_worlds 1=child_namespace /\
    forall query,query<>0%nat ->query<>1%nat ->
      final query=entry_initial_cursor query /\final_worlds query=entry_initial_worlds query.
Proof.
  intros PARENT CHILD COMMON BODY CHILD_EVENTS QUIET PARENT_RECORDING CHILD_RECORDING PREFIX TAIL.
  eapply(entry_recording_process_schedule namespace_id parent child
    (source_fork_common _ _ fork++[namespace_forked(Int.repr 2)])parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace worker_prefix worker_tail after);try eassumption.
  - rewrite(source_fork_events _ _ fork),BODY;rewrite <-app_assoc;reflexivity.
  - rewrite length_app,COMMON,preparation_common_length;reflexivity.
Qed.

Lemma entry_fork_context_is_born namespace_id:
  launch_child_context entry_fork_process namespace_id=
    LeanCage_Entry_CallerPhysical_born(Nat_of_nat namespace_id)(ProcessImport.Option_none_inst1 Lean.Nat).
Proof. reflexivity. Qed.

Theorem entry_recording_journal namespace_id parent child parent_prefix parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace worker_prefix worker_tail mayTrace after:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_events parent=parent_prefix++map namespace_process parent_events ->length parent_prefix=61%nat ->
  source_events child=map namespace_process child_events ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  RecordedRun[parent;child]mayTrace launch_recording_owner launch_recording_child
    (launch_child_context entry_worker_process namespace_id)worker_prefix(launch_parent_context entry_stopped_process namespace_id) ->
  RecordedRun[parent;child]mayTrace launch_recording_owner launch_recording_child
    (launch_parent_context entry_admitted_process namespace_id)worker_tail after ->
  RecordedRun[parent;child]mayTrace launch_recording_owner launch_recording_child
    (LeanCage_Entry_CallerPhysical_born(Nat_of_nat namespace_id)(ProcessImport.Option_none_inst1 Lean.Nat))
    (child_ticks++worker_prefix++parent_ticks++worker_tail)after.
Proof.
  intros PARENT CHILD PARENT_EVENTS PARENT_LENGTH CHILD_EVENTS PARENT_RECORDING CHILD_RECORDING PREFIX TAIL.
  assert(CHILD_DECOMPOSE:source_events child=[]++map namespace_process child_events++[])
    by(rewrite CHILD_EVENTS;cbn;rewrite app_nil_r;reflexivity).
  pose proof(child_recording_journal _ _ _ _ _ _ _ _ _ _ _ CHILD_RECORDING
    [parent;child]child mayTrace[][](Logic.eq_refl _)CHILD CHILD_DECOMPOSE(Logic.eq_refl _))as CHILD_RUN.
  rewrite entry_fork_context_is_born in CHILD_RUN.
  assert(PARENT_DECOMPOSE:source_events parent=parent_prefix++map namespace_process parent_events++[])
    by(rewrite PARENT_EVENTS,app_nil_r;reflexivity).
  pose proof(parent_recording_journal _ _ _ _ _ _ _ _ _ _ _ PARENT_RECORDING
    [parent;child]parent mayTrace parent_prefix[](Logic.eq_refl _)PARENT PARENT_DECOMPOSE PARENT_LENGTH)as PARENT_RUN.
  eapply recorded_run_append;[exact CHILD_RUN|].
  eapply recorded_run_append;[exact PREFIX|].
  eapply recorded_run_append;[exact PARENT_RUN|exact TAIL].
Qed.

Theorem entry_actual_journal namespace_id parent child(fork:ActualSourceFork parent(Int.repr 2))pair
    parent_events child_events parent_ticks child_ticks parent_namespace child_namespace worker_prefix worker_tail mayTrace after:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_fork_common _ _ fork=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10) ->
  source_fork_body _ _ fork=map namespace_process parent_events ->
  source_events child=map namespace_process child_events ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  RecordedRun[parent;child]mayTrace launch_recording_owner launch_recording_child
    (launch_child_context entry_worker_process namespace_id)worker_prefix(launch_parent_context entry_stopped_process namespace_id) ->
  RecordedRun[parent;child]mayTrace launch_recording_owner launch_recording_child
    (launch_parent_context entry_admitted_process namespace_id)worker_tail after ->
  LeanCage_Entry_CallerPhysical_Journal mayTrace launch_recording_owner launch_recording_child
    (caller_request_values(source_runs_history[parent;child]))
    (LeanCage_Entry_CallerPhysical_born(Nat_of_nat namespace_id)(ProcessImport.Option_none_inst1 Lean.Nat))
    (tick_values(child_ticks++worker_prefix++parent_ticks++worker_tail))after.
Proof.
  intros PARENT CHILD COMMON BODY CHILD_EVENTS PARENT_RECORDING CHILD_RECORDING PREFIX TAIL.
  apply actual_source_produces_journal.
  eapply(entry_recording_journal namespace_id parent child
    (source_fork_common _ _ fork++[namespace_forked(Int.repr 2)])parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace worker_prefix worker_tail mayTrace after);try eassumption.
  - rewrite(source_fork_events _ _ fork),BODY;rewrite <-app_assoc;reflexivity.
  - rewrite length_app,COMMON,preparation_common_length;reflexivity.
Qed.

Lemma entry_program_owners parent child:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  SourceProgramOwner[parent;child]launch_recording_owner 0 /\SourceProgramOwner[parent;child]launch_recording_child 1.
Proof.
  intros PARENT CHILD.
  assert(DIFFERENT:launch_recording_owner<>launch_recording_child).
  { intro SAME;pose proof(f_equal physical_identity_task SAME)as TASK.
    rewrite launch_recording_owner_task,launch_recording_child_task in TASK;discriminate. }
  assert(UNIQUE:NoDup(map source_actor[parent;child])).
  { change(NoDup[source_actor parent;source_actor child]);rewrite PARENT,CHILD.
    constructor;[cbn;intuition|constructor;[cbn;tauto|constructor]]. }
  split;eapply source_distinct_tasks_own_program;[exact UNIQUE|reflexivity|exact PARENT|
    exact UNIQUE|reflexivity|exact CHILD].
Qed.

Record EntryRecordedComposition namespace_id parent child(fork:ActualSourceFork parent(Int.repr 2))pair
    (parent_events child_events:list process_event)parent_namespace child_namespace ticks after_process
    native metadata external can_acquire after_capabilities mayTrace after_context:Type:={
  entry_composed_cursor:nat->nat;
  entry_composed_worlds:nat->NamespaceWorld;
  entry_composed_parent_program:SourceProgramOwner[parent;child]launch_recording_owner 0;
  entry_composed_child_program:SourceProgramOwner[parent;child]launch_recording_child 1;
  entry_composed_prepared:UsefulPreparedSource parent fork pair;
  entry_composed_processes:SourceProcessSchedule launch_operation launch_group_objects launch_recording_child[parent;child]0
    (UsefulEntryOther launch_group_objects[parent;child])entry_initial_cursor entry_initial_worlds entry_fork_process
    ticks entry_composed_cursor entry_composed_worlds after_process;
  entry_composed_birth:CapabilityBirth launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child pair_capability_model fork_capability_model fork_fixture_snapshot
    0 60 launch_fork_capabilities;
  entry_composed_capabilities:CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child launch_fork_capabilities ticks after_capabilities;
  entry_composed_journal:LeanCage_Entry_CallerPhysical_Journal mayTrace launch_recording_owner launch_recording_child
    (caller_request_values(source_runs_history[parent;child]))
    (LeanCage_Entry_CallerPhysical_born(Nat_of_nat namespace_id)(ProcessImport.Option_none_inst1 Lean.Nat))(tick_values ticks)after_context;
  entry_composed_requests:LeanCage_Entry_CallerRequestsAllowed(caller_request_values(source_runs_history[parent;child]));
  entry_composed_other_contract:SourceOtherContract(UsefulEntryOther launch_group_objects[parent;child])launch_group_objects
    (physical_identity_task launch_recording_owner)(physical_identity_task launch_recording_child);
  entry_composed_parent_cursor:entry_composed_cursor 0=(61+length parent_events)%nat;
  entry_composed_child_cursor:entry_composed_cursor 1=length child_events;
  entry_composed_parent_world:entry_composed_worlds 0=parent_namespace;
  entry_composed_child_world:entry_composed_worlds 1=child_namespace
}.

Arguments entry_composed_cursor {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_worlds {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_parent_program {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_child_program {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_prepared {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_processes {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_birth {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_capabilities {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_journal {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_requests {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_other_contract {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_parent_cursor {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_child_cursor {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_parent_world {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.
Arguments entry_composed_child_world {namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace ticks after_process native metadata external can_acquire after_capabilities mayTrace after_context} _.

Theorem entry_actual_recorded_composition namespace_id parent child(fork:ActualSourceFork parent(Int.repr 2))pair
    parent_events child_events parent_ticks child_ticks parent_namespace child_namespace worker_prefix worker_tail after_process
    native metadata external can_acquire after_capabilities mayTrace after_context:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_fork_common _ _ fork=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10) ->
  source_fork_body _ _ fork=map namespace_process parent_events ->
  source_events child=map namespace_process child_events ->namespace_table child_namespace=fork_fixture_worker_table ->
  Forall(fun event=>namespace_socket_io event=None)(source_events child) ->UsefulPreparedSource parent fork pair ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  CapabilityBirth launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child pair_capability_model fork_capability_model fork_fixture_snapshot
    0 60 launch_fork_capabilities ->
  UsefulWorkerRun entry_worker_process worker_prefix entry_stopped_process ->
  UsefulWorkerRun entry_admitted_process worker_tail after_process ->
  CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child(parent_recording_capabilities fork_fixture_worker_table fork_fixture_world)
    worker_prefix(parent_recording_capabilities fork_fixture_worker_table fork_fixture_world) ->
  CapabilityHistory launch_operation launch_group_objects[parent;child]native metadata external can_acquire
    launch_recording_owner launch_recording_child(parent_recording_capabilities fork_fixture_worker_table parent_namespace)
    worker_tail after_capabilities ->
  RecordedRun[parent;child]mayTrace launch_recording_owner launch_recording_child
    (launch_child_context entry_worker_process namespace_id)worker_prefix(launch_parent_context entry_stopped_process namespace_id) ->
  RecordedRun[parent;child]mayTrace launch_recording_owner launch_recording_child
    (launch_parent_context entry_admitted_process namespace_id)worker_tail after_context ->
  inhabited(EntryRecordedComposition namespace_id parent child fork pair parent_events child_events parent_namespace child_namespace
    (child_ticks++worker_prefix++parent_ticks++worker_tail)after_process native metadata external can_acquire after_capabilities mayTrace after_context).
Proof.
  intros PARENT CHILD COMMON BODY CHILD_EVENTS CHILD_TABLE QUIET PREPARED PARENT_RECORDING CHILD_RECORDING BIRTH
    PREFIX_PROCESS TAIL_PROCESS PREFIX_CAPABILITIES TAIL_CAPABILITIES PREFIX_JOURNAL TAIL_JOURNAL.
  destruct(entry_actual_process_schedule namespace_id parent child fork pair parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace worker_prefix worker_tail after_process PARENT CHILD COMMON BODY CHILD_EVENTS QUIET
    PARENT_RECORDING CHILD_RECORDING PREFIX_PROCESS TAIL_PROCESS)
    as[final[final_worlds[PROCESSES[PARENT_CURSOR[CHILD_CURSOR[PARENT_WORLD[CHILD_WORLD OTHER]]]]]]].
  destruct(entry_program_owners _ _ PARENT CHILD)as[PARENT_OWNER CHILD_OWNER].
  constructor;refine{|entry_composed_cursor:=final;entry_composed_worlds:=final_worlds;
    entry_composed_parent_program:=PARENT_OWNER;entry_composed_child_program:=CHILD_OWNER;
    entry_composed_prepared:=PREPARED;entry_composed_processes:=PROCESSES;entry_composed_birth:=BIRTH;
    entry_composed_parent_cursor:=PARENT_CURSOR;entry_composed_child_cursor:=CHILD_CURSOR;
    entry_composed_parent_world:=PARENT_WORLD;entry_composed_child_world:=CHILD_WORLD|}.
  - eapply entry_actual_capability_history;eassumption.
  - eapply entry_actual_journal;eassumption.
  - apply source_runs_history_checked.
  - rewrite launch_recording_owner_task,launch_recording_child_task;apply useful_entry_other_contract.
Qed.

Theorem entry_parent_recording_io groups program namespace_id child_table ordinal namespace world events ticks after_namespace after_world:
  ParentRecording groups program namespace_id child_table ordinal namespace world events ticks after_namespace after_world ->
  forall runs run prefix suffix,nth_error runs program=Some run ->source_actor run=launch_recording_owner ->
    source_events run=prefix++map namespace_process events++suffix ->length prefix=ordinal ->Forall(SourceIO runs)ticks.
Proof.
  intro RUN;induction RUN;intros runs run prefix suffix PROGRAM ACTOR EVENTS LENGTH;[constructor|].
  assert(EVENT:nth_error(source_events run)ordinal=Some(namespace_process event)).
  { rewrite <-LENGTH,EVENTS;apply recording_head_event. }
  constructor.
  - unfold tick,launch_parent_tick;eapply launch_recorded_source_io;eassumption.
  - eapply IHRUN with(run:=run)(prefix:=prefix++[namespace_process event])(suffix:=suffix);try eassumption.
    + rewrite EVENTS;cbn[map];repeat rewrite <-app_assoc;reflexivity.
    + rewrite length_app;cbn;lia.
Qed.

Theorem entry_child_recording_io groups program namespace_id parent_table ordinal namespace world events ticks after_namespace after_world:
  ChildRecording groups program namespace_id parent_table ordinal namespace world events ticks after_namespace after_world ->
  forall runs run prefix suffix,nth_error runs program=Some run ->source_actor run=launch_recording_child ->
    source_events run=prefix++map namespace_process events++suffix ->length prefix=ordinal ->Forall(SourceIO runs)ticks.
Proof.
  intro RUN;induction RUN;intros runs run prefix suffix PROGRAM ACTOR EVENTS LENGTH;[constructor|].
  assert(EVENT:nth_error(source_events run)ordinal=Some(namespace_process event)).
  { rewrite <-LENGTH,EVENTS;apply recording_head_event. }
  constructor.
  - unfold tick,launch_child_tick;eapply launch_recorded_source_io;eassumption.
  - eapply IHRUN with(run:=run)(prefix:=prefix++[namespace_process event])(suffix:=suffix);try eassumption.
    + rewrite EVENTS;cbn[map];repeat rewrite <-app_assoc;reflexivity.
    + rewrite length_app;cbn;lia.
Qed.

Lemma entry_worker_recording_io runs before ticks after:
  UsefulWorkerRun before ticks after ->Forall(SourceIO runs)ticks.
Proof.
  intro RUN;induction RUN;[constructor|]. constructor;[|exact IHRUN].
  intros actor fd bytes lost SOCKET;apply write_outside_c_source;[|exact SOCKET].
  eapply useful_worker_source_none;exact H.
Qed.

Lemma entry_referenced_origins owner child tick program ordinal:
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick.
Proof.
  intros SOURCE actor fd bytes lost SOCKET;left.
  exists(LeanCage_Entry_CallerPhysical_SourceReference_mk(Nat_of_nat program)(Nat_of_nat ordinal));rewrite SOURCE;constructor.
Qed.

Theorem entry_parent_recording_origins groups program namespace_id child_table ordinal namespace world events ticks after_namespace after_world:
  ParentRecording groups program namespace_id child_table ordinal namespace world events ticks after_namespace after_world ->
  forall owner child offset tick,nth_error ticks offset=Some tick ->
    LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick.
Proof.
  intro RUN;induction RUN;intros owner child[|offset]actual SELECTED;try discriminate.
  - inversion SELECTED;subst actual;eapply entry_referenced_origins;reflexivity.
  - eapply IHRUN;exact SELECTED.
Qed.

Theorem entry_child_recording_origins groups program namespace_id parent_table ordinal namespace world events ticks after_namespace after_world:
  ChildRecording groups program namespace_id parent_table ordinal namespace world events ticks after_namespace after_world ->
  forall owner child offset tick,nth_error ticks offset=Some tick ->
    LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick.
Proof.
  intro RUN;induction RUN;intros owner child[|offset]actual SELECTED;try discriminate.
  - inversion SELECTED;subst actual;eapply entry_referenced_origins;reflexivity.
  - eapply IHRUN;exact SELECTED.
Qed.

Definition EntryNoSocketWrite(tick:LeanCage_Entry_CallerPhysical_Tick):Prop:=forall actor fd bytes lost,
  ProcessImport.socket tick<>LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost.

Lemma entry_quiet_origins owner child tick:
  EntryNoSocketWrite tick ->LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick.
Proof.
  intros QUIET actor fd bytes lost SOCKET.
  assert(ACTUAL:ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost)
    by(destruct SOCKET;reflexivity).
  contradiction(QUIET _ _ _ _ ACTUAL).
Qed.

Lemma entry_origins_append owner child prefix suffix:
  (forall offset tick,nth_error prefix offset=Some tick ->LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick) ->
  (forall offset tick,nth_error suffix offset=Some tick ->LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick) ->
  forall offset tick,nth_error(prefix++suffix)offset=Some tick ->LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick.
Proof.
  intros FIRST SECOND offset tick SELECTED;destruct(lt_dec offset(length prefix))as[BEFORE|AFTER].
  - rewrite nth_error_app1 in SELECTED by exact BEFORE;eapply FIRST;exact SELECTED.
  - rewrite nth_error_app2 in SELECTED by lia;eapply SECOND;exact SELECTED.
Qed.

Record EntryIORecording runs owner child ticks:Type:={
  entry_recorded_io:forall offset tick,nth_error ticks offset=Some tick ->SourceIO runs tick;
  entry_recorded_origins:forall offset tick,nth_error ticks offset=Some tick ->
    LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick
}.
Arguments entry_recorded_io {runs owner child ticks} _.
Arguments entry_recorded_origins {runs owner child ticks} _.

Theorem entry_actual_io_recording namespace_id parent child(fork:ActualSourceFork parent(Int.repr 2))pair
    parent_events child_events parent_ticks child_ticks parent_namespace child_namespace worker_prefix worker_tail after:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_fork_common _ _ fork=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10) ->
  source_fork_body _ _ fork=map namespace_process parent_events ->source_events child=map namespace_process child_events ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  UsefulWorkerRun entry_worker_process worker_prefix entry_stopped_process ->UsefulWorkerRun entry_admitted_process worker_tail after ->
  Forall EntryNoSocketWrite worker_prefix ->Forall EntryNoSocketWrite worker_tail ->
  inhabited(EntryIORecording[parent;child]launch_recording_owner launch_recording_child
    (child_ticks++worker_prefix++parent_ticks++worker_tail)).
Proof.
  intros PARENT CHILD COMMON BODY CHILD_EVENTS PARENT_RECORDING CHILD_RECORDING PREFIX TAIL PREFIX_QUIET TAIL_QUIET.
  assert(CHILD_DECOMPOSE:source_events child=[]++map namespace_process child_events++[])
    by(rewrite CHILD_EVENTS;cbn;rewrite app_nil_r;reflexivity).
  pose proof(entry_child_recording_io _ _ _ _ _ _ _ _ _ _ _ CHILD_RECORDING[parent;child]child[][]
    (Logic.eq_refl _)CHILD CHILD_DECOMPOSE(Logic.eq_refl _))as CHILD_IO.
  assert(PARENT_DECOMPOSE:source_events parent=(source_fork_common _ _ fork++[namespace_forked(Int.repr 2)])++
    map namespace_process parent_events++[]).
  { rewrite(source_fork_events _ _ fork),BODY,app_nil_r;rewrite <-app_assoc;reflexivity. }
  assert(LENGTH:length(source_fork_common _ _ fork++[namespace_forked(Int.repr 2)])=61).
  { rewrite length_app,COMMON,preparation_common_length;reflexivity. }
  pose proof(entry_parent_recording_io _ _ _ _ _ _ _ _ _ _ _ PARENT_RECORDING[parent;child]parent
    (source_fork_common _ _ fork++[namespace_forked(Int.repr 2)])[](Logic.eq_refl _)PARENT PARENT_DECOMPOSE LENGTH)as PARENT_IO.
  assert(ALL_IO:Forall(SourceIO[parent;child])(child_ticks++worker_prefix++parent_ticks++worker_tail)).
  { repeat(apply Forall_app;split);try assumption;[eapply entry_worker_recording_io;exact PREFIX|
      eapply entry_worker_recording_io;exact TAIL]. }
  constructor;constructor.
  - intros offset tick SELECTED;rewrite Forall_forall in ALL_IO;apply ALL_IO;eapply nth_error_In;exact SELECTED.
  - eapply entry_origins_append;[eapply entry_child_recording_origins;exact CHILD_RECORDING|].
    eapply entry_origins_append.
    + intros offset tick SELECTED;apply entry_quiet_origins;rewrite Forall_forall in PREFIX_QUIET;apply PREFIX_QUIET.
      eapply nth_error_In;exact SELECTED.
    + eapply entry_origins_append;[eapply entry_parent_recording_origins;exact PARENT_RECORDING|].
      intros offset tick SELECTED;apply entry_quiet_origins;rewrite Forall_forall in TAIL_QUIET;apply TAIL_QUIET.
      eapply nth_error_In;exact SELECTED.
Qed.

Theorem entry_primitive_ticks_no_write family tables context frames:
  Forall EntryNoSocketWrite(entry_primitive_ticks family tables context frames).
Proof.
  induction frames as[|frame frames IH];cbn[entry_primitive_ticks map];[constructor|].
  constructor;[|exact IH].
  intros actor fd bytes lost;apply entry_primitive_no_socket_write.
Qed.

Theorem entry_worker_prefix_no_write tables:Forall EntryNoSocketWrite(entry_worker_prefix tables).
Proof.
  unfold entry_worker_prefix.
  apply Forall_app;split;[apply entry_primitive_ticks_no_write|].
  apply Forall_app;split;[apply entry_primitive_ticks_no_write|].
  apply Forall_app;split;[apply entry_primitive_ticks_no_write|].
  constructor;[unfold entry_trace_tick;intros actor fd bytes lost;apply entry_primitive_no_socket_write|].
  constructor;[unfold entry_stop_tick;intros actor fd bytes lost;apply entry_primitive_no_socket_write|constructor].
Qed.

Theorem entry_worker_tail_no_write tables:Forall EntryNoSocketWrite(entry_worker_tail tables).
Proof. apply entry_primitive_ticks_no_write. Qed.

Theorem entry_concrete_io_recording parent child(fork:ActualSourceFork parent(Int.repr 2))pair
    parent_events child_events parent_ticks child_ticks parent_namespace child_namespace prefix_tables tail_tables:
  source_actor parent=launch_recording_owner ->source_actor child=launch_recording_child ->
  source_fork_common _ _ fork=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10) ->
  source_fork_body _ _ fork=map namespace_process parent_events ->source_events child=map namespace_process child_events ->
  ParentRecording launch_group_objects 0 1 fork_fixture_worker_table 61 fork_fixture_world entry_stopped_process
    parent_events parent_ticks parent_namespace entry_admitted_process ->
  ChildRecording launch_group_objects 1 1(namespace_table fork_fixture_world)0 child_fork_namespace entry_fork_process
    child_events child_ticks child_namespace entry_worker_process ->
  inhabited(EntryIORecording[parent;child]launch_recording_owner launch_recording_child
    (child_ticks++entry_worker_prefix prefix_tables++parent_ticks++entry_worker_tail tail_tables)).
Proof.
  intros PARENT CHILD COMMON BODY CHILD_EVENTS PARENT_RECORDING CHILD_RECORDING.
  eapply(entry_actual_io_recording 1 parent child fork pair parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace(entry_worker_prefix prefix_tables)(entry_worker_tail tail_tables)entry_admitted_process);try eassumption.
  - apply entry_worker_prefix_process.
  - apply entry_worker_tail_process.
  - apply entry_worker_prefix_no_write.
  - apply entry_worker_tail_no_write.
Qed.
