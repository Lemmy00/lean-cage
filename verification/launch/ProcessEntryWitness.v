(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: One actual prepared source supplies both branches and capability birth. *)
From Stdlib Require Import ZArith List Lia FunctionalExtensionality.
From compcert Require Import Integers Values Memory Globalenvs Ctypes Clight.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput NativeHandoffInputWitness.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessSourceTables ProcessLaunchWitness ProcessLaunchRecordingWitness
  ProcessParentRecordingWitness ProcessChildRecordingWitness ProcessChildTickWitness
  ProcessChildOtherWitness ProcessParentCapabilityWitness ProcessCapabilityRecording ProcessCapabilityBirth
  ProcessPreparationWitness.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespacePaths NamespaceKernel NamespaceWorldTrace NamespacePhysical
  NamespaceFork NamespaceForkWitness NamespaceForkWorldWitness NamespaceChildWorldWitness NamespaceWitnessConnection NamespaceSourceFork
  NamespaceParentInput NamespaceLaunchWitness NamespaceRelease NamespaceChannel NamespaceCaller NamespacePrepared NamespaceCapabilities
  NamespaceGuestFlags.
Import ListNotations.
Local Close Scope lean_scope.

Definition UsefulPreparedSource(parent:CallerSourceRun)(fork:ActualSourceFork parent(Int.repr 2))pair:Prop:=
  exists initial cell command source prepared e memory parameters final request,
    Genv.init_mem EntrySource.prog=Some initial /\source_cell parent=cell /\
    source_before parent=live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory) /\
    e=namespace_initial_env prepared /\handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    namespace_useful_preparation cell command source prepared e memory Int64.one /\
    source_fork_continuation _ _ fork=
      child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop) /\
    source_fork_parent _ _ fork=source_fork_before _ _ fork /\
    source_after parent=live(Returnstate(Vint Int.zero)
      (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final) /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters(source_fork_parent _ _ fork)
      (source_fork_body _ _ fork)final request).

Lemma entry_fork_capabilities_are_child:
  launch_fork_capabilities=
    child_recording_capabilities(namespace_table fork_fixture_world)child_fork_namespace.
Proof.
  unfold launch_fork_capabilities,capability_retable,preparation_capabilities,child_recording_capabilities;
    cbn[capability_tables capability_messages];f_equal;apply functional_extensionality;intro actor.
  unfold task_table_put,preparation_tables,launch_child_tables.
  destruct(Nat.eq_dec actor 1)as[ONE|ONE];[subst actor;reflexivity|].
  assert(NE1:Nat.eqb actor 1=false)by(apply Nat.eqb_neq;exact ONE);rewrite NE1.
  destruct(Nat.eqb actor 2);reflexivity.
Qed.

Lemma entry_child_capabilities_are_parent namespace:
  namespace_table namespace=fork_fixture_worker_table ->
  child_recording_capabilities(namespace_table fork_fixture_world)namespace=
    parent_recording_capabilities fork_fixture_worker_table fork_fixture_world.
Proof.
  intro TABLE;unfold child_recording_capabilities,parent_recording_capabilities;
    f_equal;apply functional_extensionality;intro actor.
  unfold launch_child_tables,launch_parent_tables;rewrite TABLE.
  destruct(Nat.eqb actor 1), (Nat.eqb actor 2), (Nat.eqb actor 3);reflexivity.
Qed.

Theorem actual_useful_source_recording_chain(namespace_id:nat):
  exists parent child:CallerSourceRun,exists fork:ActualSourceFork parent(Int.repr 2),
  exists pair parent_events child_events parent_ticks child_ticks parent_namespace child_namespace b image_memory image_world,
    source_actor parent=launch_recording_owner /\source_actor child=launch_recording_child /\
    SourceProgramOwner[parent;child]launch_recording_owner 0 /\
    SourceProgramOwner[parent;child]launch_recording_child 1 /\
    source_fork_common _ _ fork=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10) /\
    source_fork_body _ _ fork=map namespace_process parent_events /\
    source_events child=map namespace_process child_events /\
    source_before child=live(Returnstate(Vint Int.zero)(source_fork_continuation _ _ fork)(source_fork_before _ _ fork)) /\
    source_after child=dead image_memory /\
    NativeForkCopy(source_cell parent)(source_fork_before _ _ fork)(source_fork_parent _ _ fork)(source_fork_before _ _ fork) /\
    ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world
      (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)
      parent_events parent_ticks parent_namespace
      (launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1%nat)) /\
    ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace
      (launch_world launch_fork_files None task_running Int64.zero None)child_events child_ticks child_namespace
      (launch_world launch_parent_files None task_running Int64.zero None) /\
    namespace_table child_namespace=fork_fixture_worker_table /\
    namespace_worker_ordinary_input b image_memory image_world /\
    namespace_table image_world=namespace_table child_namespace /\
    Forall(fun event=>NamespaceSocket.namespace_socket_io event=None)(source_events child) /\
    UsefulPreparedSource parent fork pair /\
    source_cell child=source_cell parent /\
    In(namespace_guest_event(entry_image
      (Vptr(NativeHandoffArguments.handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
      (Vptr(NativeHandoffAllocation.handoff_arguments b)Ptrofs.zero)
      (Vptr(NativeHandoffAllocation.handoff_environment b)Ptrofs.zero)))(source_events child) /\
    forall native metadata external can_acquire,
      CapabilityBirth launch_operation launch_group_objects[parent;child]native metadata external can_acquire
        launch_recording_owner launch_recording_child pair_capability_model fork_capability_model fork_fixture_snapshot
        0 60 launch_fork_capabilities.
Proof.
  destruct namespace_actual_source_ordinary_entry_shaped_prepared as(initial &cell &command &source &prepared &e &memory &pair &fork_memory
    &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY
    &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &CHILD_IMAGE &SHAPE &PREPARATION).
  destruct SHAPE as[shape].
  destruct CHILD_IMAGE as(branch_memory &b &image_memory &caller &prefix &image_world &FIELDS &ORDINARY).
  pose proof FIELDS as(BRANCH_BORROW &SNAPSHOT &BYTES &CANONICAL_IMAGE &CHILD_SOURCE &GUEST &KERNEL &TABLE &EXACT &CHLD &MASK).
  set(common:=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10)).
  set(continuation:=child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop)).
  set(root:=live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory)).
  set(fork_call:=live(Callstate namespace_fork_definition[]continuation fork_memory)).
  set(parent_return:=live(Returnstate(Vint(Int.repr 2))continuation fork_memory)).
  set(child_return:=live(Returnstate(Vint Int.zero)continuation fork_memory)).
  set(parent_after:=live(Returnstate(Vint Int.zero)
    (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final)).
  assert(DIFFERENT:launch_recording_owner<>launch_recording_child).
  { intro SAME;pose proof(f_equal physical_identity_task SAME)as TASK.
    rewrite launch_recording_owner_task,launch_recording_child_task in TASK;discriminate TASK. }
  pose(actual_fork_caller_runs launch_recording_owner launch_recording_child cell root common fork_call parent_return
    child_return suffix parent_after(child_useful_namespace_events b prefix)(dead image_memory)(Int.repr 2)
    DIFFERENT STARTED COMMON PARENT CHILD GRANT CHILD_SOURCE)as calls.
  set(parent:=fork_parent_run _ _ _ _ _ _ _ _ _ _ _ calls).
  set(child:=fork_child_run _ _ _ _ _ _ _ _ _ _ _ calls).
  assert(PARENT_CELL:source_cell parent=cell)by(subst parent;apply fork_parent_cell).
  assert(PARENT_BEFORE:source_before parent=root)by(subst parent;apply fork_parent_before).
  assert(PARENT_AFTER:source_after parent=parent_after)by(subst parent;apply fork_parent_after).
  assert(PARENT_EVENTS:source_events parent=common++namespace_forked(Int.repr 2)::suffix).
  { subst parent;apply fork_parent_events. }
  assert(PARENT_ACTOR:source_actor parent=launch_recording_owner)by(subst parent;apply fork_parent_actor).
  assert(CHILD_ACTOR:source_actor child=launch_recording_child)by(subst child;apply fork_child_actor).
  assert(CHILD_EVENTS:source_events child=child_useful_namespace_events b prefix)by(subst child;apply fork_child_events).
  assert(CHILD_BEFORE:source_before child=child_return)by(subst child;apply fork_child_before).
  assert(CHILD_AFTER:source_after child=dead image_memory)by(subst child;apply fork_child_after).
  assert(PARENT_PROGRAM:SourceProgramOwner[parent;child]launch_recording_owner 0).
  { subst parent child;apply fork_parent_program. }
  assert(CHILD_PROGRAM:SourceProgramOwner[parent;child]launch_recording_child 1).
  { subst parent child;apply fork_child_program. }
  assert(FORK_PREFIX:namespace_steps ProcessGlobalCalls.caller_ge(source_cell parent)(source_before parent)common
    (live(Callstate namespace_fork_definition[]continuation fork_memory))).
  { rewrite PARENT_CELL,PARENT_BEFORE;exact COMMON. }
  assert(FORK_OPERATION:namespace_step ProcessGlobalCalls.caller_ge(source_cell parent)
    (live(Callstate namespace_fork_definition[]continuation fork_memory))(namespace_forked(Int.repr 2))
    (live(Returnstate(Vint(Int.repr 2))continuation fork_memory))).
  { rewrite PARENT_CELL;exact PARENT. }
  assert(FORK_SUFFIX:namespace_steps ProcessGlobalCalls.caller_ge(source_cell parent)
    (live(Returnstate(Vint(Int.repr 2))continuation fork_memory))suffix(source_after parent)).
  { rewrite PARENT_CELL,PARENT_AFTER;exact GRANT. }
  set(fork:={|source_fork_common:=common;source_fork_body:=suffix;source_fork_continuation:=continuation;
    source_fork_before:=fork_memory;source_fork_parent:=fork_memory;source_fork_events:=PARENT_EVENTS;
    source_fork_prefix:=FORK_PREFIX;source_fork_operation:=FORK_OPERATION;source_fork_suffix:=FORK_SUFFIX|}:
    ActualSourceFork parent(Int.repr 2)).
  destruct(launch_actual_parent_file_timeline _ _ _ _ _ _ _ _ shape)as[parent_events[parent_namespace[PARENT_MAP PARENT_FILE]]].
  destruct(launch_parent_recording _ _ _ _ _ _ PARENT_FILE(Logic.eq_refl _)launch_actual_fork_nonnegative
    (Logic.eq_refl _)ltac:(discriminate)0 61 namespace_id fork_fixture_worker_table)as[parent_ticks PARENT_RECORDING].
  destruct(actual_same_fork_child_ticks _ _ _ _ _ _ _ _ _ _ _ _ _ namespace_id FIELDS)
    as[child_events[child_namespace[child_ticks[CHILD_MAP[CHILD_TABLE CHILD_RECORDING]]]]].
  exists parent,child,fork,pair,parent_events,child_events,parent_ticks,child_ticks,parent_namespace,child_namespace,
    b,image_memory,image_world.
  split;[exact PARENT_ACTOR|]. split;[exact CHILD_ACTOR|]. split;[exact PARENT_PROGRAM|]. split;[exact CHILD_PROGRAM|].
  split;[reflexivity|]. split;[exact PARENT_MAP|]. split;[rewrite CHILD_EVENTS;exact CHILD_MAP|].
  split;[exact CHILD_BEFORE|]. split;[exact CHILD_AFTER|]. split;[rewrite PARENT_CELL;exact COPY|].
  split;[exact PARENT_RECORDING|]. split;[exact CHILD_RECORDING|]. split;[exact CHILD_TABLE|].
  split;[exact ORDINARY|]. split;[rewrite TABLE,CHILD_TABLE;reflexivity|]. split.
  - rewrite CHILD_EVENTS;eapply actual_same_fork_child_sockets_none;exact FIELDS.
  - split.
    + exists initial,cell,command,source,prepared,e,memory,parameters,final,request.
      split;[exact INITIAL|]. split;[exact PARENT_CELL|]. split;[exact PARENT_BEFORE|].
      split;[exact CANONICAL|]. split;[exact INPUT|]. split;[exact PREPARATION|].
      split;[reflexivity|]. split;[reflexivity|]. split;[exact PARENT_AFTER|]. constructor;exact shape.
    + split.
      * rewrite PARENT_CELL;subst child;apply fork_child_cell.
      * split.
        -- rewrite CHILD_EVENTS;unfold child_useful_namespace_events;apply in_or_app;right.
           apply in_map;apply in_or_app;right;left;reflexivity.
        -- intros native metadata external can_acquire;eapply preparation_actual_capability_birth with(run:=parent)
             (namespace_id:=namespace_id)(pair:=pair)(parent_tail:=suffix);[reflexivity|exact PARENT_ACTOR|exact PARENT_EVENTS].
Qed.
