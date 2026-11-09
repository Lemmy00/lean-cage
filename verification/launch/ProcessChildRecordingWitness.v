(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Bind inherited child authority to its actual source and image. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import AST Integers Values Memory Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine CallContexts.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput NativeHandoffArguments
  NativeHandoffTraceEvents NativeHandoffTrace.
From EntryProcess Require Import ProcessMachine ProcessOwnership ProcessPhysicalTrace ProcessPhysicalWitness
  ProcessLaunchWitness ProcessSourceRecording ProcessPaths.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace
  NamespaceGuestFlags NamespaceGuestImage NamespaceForkWorldWitness NamespaceChildWorldWitness NamespacePaths.
Import ListNotations.
Open Scope Z_scope.

(* The accepted projection retains unexpected operations. Its actual good
   prefix therefore selects precisely source/formatter/flag/wait operations. *)
Lemma child_flagged_operation event:
  Forall namespace_good_flag(handoff_event_flags event) ->
  launch_operation physical_child(launch_world launch_fork_files None task_running Int64.zero None)
    (process_entry event)(launch_world launch_fork_files None task_running Int64.zero None).
Proof.
  destruct event;cbn[handoff_event_flags];intro GOOD;
    try solve[inversion GOOD;contradiction];try solve[apply launch_neutral;reflexivity].
  - destruct event;cbn[handoff_event_flags]in GOOD|-*;
      try solve[inversion GOOD;contradiction];try solve[apply launch_neutral;reflexivity].
    destruct ev;cbn[handoff_event_flags]in GOOD|-*;
      try solve[inversion GOOD;contradiction];try solve[apply launch_neutral;reflexivity].
  - inversion GOOD as[|tag rest HEAD TAIL];subst.
    cbn[namespace_good_flag]in HEAD;destruct HEAD as[RETURNED FLAGS];subst returned.
    apply launch_flags;exact FLAGS.
Qed.

Lemma child_flagged_not_image event:
  Forall namespace_good_flag(handoff_event_flags event) ->launch_not_image(process_entry event).
Proof. intro GOOD;destruct event;try exact I;inversion GOOD;contradiction. Qed.

Theorem child_flagged_steps events:
  Forall namespace_good_flag(handoff_flags_projection events) ->
  LaunchSteps physical_child(launch_world launch_fork_files None task_running Int64.zero None)
    (map process_entry events)(launch_world launch_fork_files None task_running Int64.zero None).
Proof.
  induction events as[|event events IH];intro GOOD;[constructor|].
  unfold handoff_flags_projection in GOOD;cbn[flat_map]in GOOD;apply Forall_app in GOOD as[HEAD TAIL].
  cbn[map];econstructor;[apply child_flagged_operation;exact HEAD|apply IH;exact TAIL].
Qed.

Lemma child_flagged_events_not_image events:
  Forall namespace_good_flag(handoff_flags_projection events) ->Forall launch_not_image(map process_entry events).
Proof.
  induction events as[|event events IH];intro GOOD;[constructor|].
  unfold handoff_flags_projection in GOOD;cbn[flat_map]in GOOD;apply Forall_app in GOOD as[HEAD TAIL].
  cbn[map];constructor;[apply child_flagged_not_image;exact HEAD|apply IH;exact TAIL].
Qed.

Theorem actual_guest_child_process_steps cell input before k events target path arguments environment:
  handoff_borrowed_input cell before input ->is_call_cont k ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 60)]k before))
    events target ->In(entry_image path arguments environment)events ->
  LaunchSteps physical_child(launch_world launch_fork_files None task_running Int64.zero None)
    (map process_entry events)(launch_world launch_parent_files None task_running Int64.zero None).
Proof.
  intros INPUT CALL SOURCE IMAGE.
  destruct(handoff_guest_image_flags _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT SOURCE IMAGE)
    as[prefix[b[after[caller[suffix[waits[EVENTS[FLAGS[PREFIX[PATH[ARGS[ENV TARGET]]]]]]]]]]]].
  assert(GOOD:Forall namespace_good_flag(handoff_flags_projection prefix)).
  { rewrite FLAGS;unfold handoff_expected_flags;repeat(apply Forall_cons;
      [cbn[namespace_good_flag];auto|]);constructor. }
  rewrite EVENTS,map_app;eapply launch_steps_append;[apply child_flagged_steps;exact GOOD|].
  rewrite map_app;eapply launch_steps_append.
  - rewrite map_repeat;apply launch_passive_steps.
    apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst event;reflexivity.
  - cbn[map];econstructor;[|constructor].
    pose proof(launch_image physical_child launch_fork_files None task_running Int64.zero None path arguments environment)as EXEC.
    rewrite launch_child_exec_drops_copied_file in EXEC;exact EXEC.
Qed.

Definition child_fork_namespace:=namespace_fork_child fork_fixture_world fork_fixture_snapshot.

Lemma child_initial_file_view:
  SourceFileView launch_group_objects(launch_world launch_fork_files None task_running Int64.zero None)
    physical_child child_fork_namespace.
Proof.
  intros fd group.
  change(launch_fork_files physical_child fd=Some group <->
    exists binding object,namespace_table fork_fixture_world fd=Some binding /\
      descriptor_object binding=ordinary_object object /\launch_group_objects object=Some group).
  assert(FILES:launch_fork_files physical_child fd=launch_parent_files physical_parent fd).
  { unfold launch_fork_files,launch_parent_files;rewrite !launch_task_eq_same,orb_true_r;reflexivity. }
  rewrite FILES;exact(launch_actual_fork_file_view fd group).
Qed.

Lemma child_file_recording_final groups actor before namespace events after final:
  LaunchFileRecording groups actor before namespace events after final ->SourceFileView groups after actor final.
Proof. intro RUN;induction RUN;assumption. Qed.

Lemma child_file_recording_kernel groups actor before namespace events after final:
  LaunchFileRecording groups actor before namespace events after final ->
  namespace_kernel_steps namespace(map namespace_process events)final.
Proof. intro RUN;induction RUN;cbn;[constructor|econstructor;eassumption]. Qed.

Lemma child_file_recording_append groups actor before namespace prefix middle boundary suffix after final:
  LaunchFileRecording groups actor before namespace prefix middle boundary ->
  LaunchFileRecording groups actor middle boundary suffix after final ->
  LaunchFileRecording groups actor before namespace(prefix++suffix)after final.
Proof. intro FIRST;induction FIRST;intro SECOND;[exact SECOND|cbn;econstructor;eauto]. Qed.

Lemma child_worker_no_cgroup fd binding:
  fork_fixture_worker_table fd=Some binding ->descriptor_object binding<>ordinary_object 103.
Proof.
  rewrite namespace_useful_worker_table_exact;unfold fork_fixture_worker_slot;intro PRESENT.
  repeat match type of PRESENT with
  |context[if ?test then _ else _]=>destruct test;try discriminate end.
  all:inversion PRESENT;subst binding;cbn;intro SAME;inversion SAME.
Qed.

Lemma child_worker_file_view namespace:
  namespace_table namespace=fork_fixture_worker_table ->
  SourceFileView launch_group_objects(launch_world launch_parent_files None task_running Int64.zero None)
    physical_child namespace.
Proof.
  intros TABLE fd group;change(launch_parent_files physical_child fd=Some group <->
    exists binding object,namespace_table namespace fd=Some binding /\
      descriptor_object binding=ordinary_object object /\launch_group_objects object=Some group).
  assert(EMPTY:launch_parent_files physical_child fd=None).
  { unfold launch_parent_files;change((if false&&Int.eq fd(Int.repr 7)then Some 1%nat else None)=None);reflexivity. }
  rewrite EMPTY,TABLE;split;[discriminate|].
  intros[binding[object[PRESENT[OBJECT CLASS]]]].
  unfold launch_group_objects in CLASS;destruct(Nat.eqb object 103)eqn:SELECTED;[|discriminate].
  apply Nat.eqb_eq in SELECTED;subst object.
  exfalso;exact(child_worker_no_cgroup _ _ PRESENT OBJECT).
Qed.

Lemma child_wait_file_recording groups namespace count:
  SourceFileView groups(launch_world launch_fork_files None task_running Int64.zero None)physical_child namespace ->
  LaunchFileRecording groups physical_child(launch_world launch_fork_files None task_running Int64.zero None)namespace
    (map process_entry(repeat entry_primitive_wait count))
    (launch_world launch_fork_files None task_running Int64.zero None)namespace.
Proof.
  intro VIEW;induction count;cbn[repeat map];[constructor;exact VIEW|].
  econstructor;[exact VIEW|apply launch_neutral;reflexivity|apply namespace_kernel_passive;reflexivity|exact IHcount].
Qed.

Theorem actual_guest_child_file_recording cell input before k events target path arguments environment:
  handoff_borrowed_input cell before input ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 60)]k before))
    events target ->In(entry_image path arguments environment)events ->
  exists final,
    LaunchFileRecording launch_group_objects physical_child
      (launch_world launch_fork_files None task_running Int64.zero None)child_fork_namespace(map process_entry events)
      (launch_world launch_parent_files None task_running Int64.zero None)final /\
    namespace_table final=fork_fixture_worker_table.
Proof.
  intros INPUT SOURCE IMAGE.
  destruct(handoff_guest_image_flags _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT SOURCE IMAGE)
    as[prefix[b[after[caller[suffix[waits[EVENTS[FLAGS[PREFIX[PATH[ARGS[ENV TARGET]]]]]]]]]]]].
  assert(GOOD:Forall namespace_good_flag(handoff_flags_projection prefix)).
  { rewrite FLAGS;unfold handoff_expected_flags;repeat(apply Forall_cons;
      [cbn[namespace_good_flag];auto|]);constructor. }
  destruct(launch_steps_have_file_recording launch_group_objects physical_child _ _ _(child_flagged_steps _ GOOD)
    (child_flagged_events_not_image _ GOOD)child_fork_namespace child_initial_file_view)
    as[at_image RECORDING].
  pose proof(child_file_recording_final _ _ _ _ _ _ _ RECORDING)as VIEW.
  pose proof(child_file_recording_kernel _ _ _ _ _ _ _ RECORDING)as KERNEL.
  rewrite map_map in KERNEL.
  change(namespace_kernel_steps child_fork_namespace(map namespace_guest_event prefix)at_image)in KERNEL.
  destruct(expected_guest_flags_determine_table _ _ _ _ _ _ _ KERNEL FLAGS)as[TABLE REST].
  assert(FINAL_TABLE:namespace_table(namespace_exec at_image default_signal_action)=fork_fixture_worker_table).
  { change(exec_table(namespace_table at_image)=fork_fixture_worker_table);rewrite TABLE;reflexivity. }
  exists(namespace_exec at_image default_signal_action);split;[|exact FINAL_TABLE].
  rewrite EVENTS,map_app;eapply child_file_recording_append;[exact RECORDING|].
  rewrite map_app;eapply child_file_recording_append;[apply child_wait_file_recording;exact VIEW|].
  cbn[map];econstructor.
  - exact VIEW.
  - pose proof(launch_image physical_child launch_fork_files None task_running Int64.zero None path arguments environment)as EXEC.
    rewrite launch_child_exec_drops_copied_file in EXEC;exact EXEC.
  - apply namespace_kernel_exec;intro;reflexivity.
  - constructor;apply child_worker_file_view;exact FINAL_TABLE.
Qed.

Lemma child_source_file_recording namespace count:
  SourceFileView launch_group_objects(launch_world launch_fork_files None task_running Int64.zero None)
    physical_child namespace ->
  LaunchFileRecording launch_group_objects physical_child
    (launch_world launch_fork_files None task_running Int64.zero None)namespace(repeat process_source_event count)
    (launch_world launch_fork_files None task_running Int64.zero None)namespace.
Proof.
  intro VIEW;induction count;cbn[repeat];[constructor;exact VIEW|].
  econstructor;[exact VIEW|apply launch_neutral;reflexivity|apply namespace_kernel_source|exact IHcount].
Qed.

Theorem actual_same_fork_child_file_recording cell command source memory pair parameters k
    branch_memory b after caller prefix world:
  namespace_useful_child_image_fields cell command source memory pair parameters k
    branch_memory b after caller prefix world ->
  exists originals final,
    ((repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3)++
      map namespace_guest_event(prefix++[entry_image(Vptr(NativeHandoffArguments.handoff_symbol ___stringlit_111)Ptrofs.zero)
        (Vptr(NativeHandoffAllocation.handoff_arguments b)Ptrofs.zero)
        (Vptr(NativeHandoffAllocation.handoff_environment b)Ptrofs.zero)]))=map namespace_process originals /\
    LaunchFileRecording launch_group_objects physical_child
      (launch_world launch_fork_files None task_running Int64.zero None)child_fork_namespace originals
      (launch_world launch_parent_files None task_running Int64.zero None)final /\
    namespace_table final=fork_fixture_worker_table.
Proof.
  intro FIELDS;unfold namespace_useful_child_image_fields in FIELDS;cbn zeta in FIELDS.
  destruct FIELDS as[BORROWED[SNAPSHOT[BYTES[CANONICAL[CHILD_SOURCE[GUEST REST]]]]]].
  assert(IMAGE:In(entry_image(Vptr(NativeHandoffArguments.handoff_symbol ___stringlit_111)Ptrofs.zero)
    (Vptr(NativeHandoffAllocation.handoff_arguments b)Ptrofs.zero)
    (Vptr(NativeHandoffAllocation.handoff_environment b)Ptrofs.zero))
    (prefix++[entry_image(Vptr(NativeHandoffArguments.handoff_symbol ___stringlit_111)Ptrofs.zero)
      (Vptr(NativeHandoffAllocation.handoff_arguments b)Ptrofs.zero)
      (Vptr(NativeHandoffAllocation.handoff_environment b)Ptrofs.zero)])).
  { apply in_or_app;right;left;reflexivity. }
  destruct(actual_guest_child_file_recording _ _ _ _ _ _ _ _ _ BORROWED GUEST IMAGE)as[final[RECORDING TABLE]].
  exists((repeat process_source_event 4++repeat process_source_event 3++repeat process_source_event 3)++
    map process_entry(prefix++[entry_image(Vptr(NativeHandoffArguments.handoff_symbol ___stringlit_111)Ptrofs.zero)
      (Vptr(NativeHandoffAllocation.handoff_arguments b)Ptrofs.zero)
      (Vptr(NativeHandoffAllocation.handoff_environment b)Ptrofs.zero)])),final.
  split.
  - rewrite !map_app,!map_repeat,map_map;reflexivity.
  - split;[|exact TABLE].
    eapply child_file_recording_append;[|exact RECORDING].
    eapply child_file_recording_append;[apply child_source_file_recording;exact child_initial_file_view|].
    eapply child_file_recording_append;apply child_source_file_recording;exact child_initial_file_view.
Qed.
