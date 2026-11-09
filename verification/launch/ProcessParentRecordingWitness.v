(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Record the actual parent's source and kernel positions together. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessSourceWorlds ProcessLaunchWitness ProcessLaunchRecordingWitness.
From EntryProcess Require Import ProcessCallerConnection.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceWorldTrace NamespacePhysical
  NamespaceDescriptorFrame NamespaceForkWorldWitness.
From EntryNamespace Require Import NamespaceSocket.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Definition launch_recording_owner:LeanCage_Entry_ProcessIdentity.
Proof. apply(source_task_identity physical_parent);change(1<=1);lia. Defined.
Definition launch_recording_child:LeanCage_Entry_ProcessIdentity.
Proof. apply(source_task_identity physical_child);change(1<=2);lia. Defined.

Lemma launch_recording_owner_task:physical_identity_task launch_recording_owner=physical_parent.
Proof. apply source_task_identity_is_same. Qed.
Lemma launch_recording_child_task:physical_identity_task launch_recording_child=physical_child.
Proof. apply source_task_identity_is_same. Qed.
Lemma launch_recording_owner_key:nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner)=1%nat.
Proof.
  rewrite <-physical_identity_task_key,launch_recording_owner_task.
  change((0*Z.to_nat 2147483648+1)%nat=1%nat);reflexivity.
Qed.

Lemma launch_recorded_source_io runs run actor program ordinal before after world event tables:
  nth_error runs program=Some run ->source_actor run=actor ->
  nth_error(source_events run)ordinal=Some event ->
  SourceIO runs(source_recording_tick actor program ordinal before after world event tables).
Proof.
  intros PROGRAM ACTOR EVENT observed fd bytes lost WROTE.
  change(source_recording_socket actor event=
    LeanCage_Entry_CallerPhysical_SocketObservation_wrote observed fd bytes lost)in WROTE.
  unfold source_recording_socket in WROTE.
  destruct(namespace_socket_io event)as[io|]eqn:SOCKET;[|discriminate].
  destruct(IO.operation(source_socket_request io))eqn:OPERATION;[discriminate|].
  inversion WROTE;subst observed fd bytes lost.
  apply write_from_source;eapply source_write_actual with(run:=run)(program:=program)(ordinal:=ordinal)(event:=event)(io:=io).
  - exact PROGRAM.
  - exact EVENT.
  - exact SOCKET.
  - exact OPERATION.
  - symmetry;exact ACTOR.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn[ProcessImport.socket source_recording_tick].
    unfold source_recording_socket;rewrite SOCKET,OPERATION;reflexivity.
  - reflexivity.
Qed.

Definition launch_parent_context(world:ProcessWorld)(namespace:nat):=
  source_recording_context launch_recording_owner true
    (owned_phase(process_tasks world physical_child))(owned_options(process_tasks world physical_child))
    namespace(owned_cgroup(process_tasks world physical_child)).

Definition launch_parent_tables(namespace:NamespaceWorld)(child:DescriptorTable)(key:nat):DescriptorTable:=
  if Nat.eqb key 1 then namespace_table namespace
  else if Nat.eqb key 2 then child
  else if Nat.eqb key 3 then fork_fixture_other else fun _=>None.

Lemma launch_parent_table_here namespace child:
  launch_parent_tables namespace child
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner))=namespace_table namespace.
Proof. rewrite launch_recording_owner_key;reflexivity. Qed.

Lemma launch_parent_context_view world namespace:
  owned_tracer(process_tasks world physical_child)=Some physical_parent ->
  SourceProcessView world(physical_identity_task launch_recording_child)(launch_parent_context world namespace).
Proof.
  intro TRACER;unfold launch_parent_context;apply source_recording_context_view;
    rewrite launch_recording_child_task;try reflexivity.
  rewrite launch_recording_owner_task;exact TRACER.
Qed.

Lemma launch_parent_context_live world namespace:
  owned_phase(process_tasks world physical_parent)<>task_exited ->
  SourceParentView world(physical_identity_task launch_recording_owner)(launch_parent_context world namespace).
Proof.
  intro LIVE;unfold launch_parent_context;apply source_recording_parent_view.
  rewrite launch_recording_owner_task;exact LIVE.
Qed.

Lemma launch_parent_operation_live before event after:
  launch_operation physical_parent before event after ->
  owned_phase(process_tasks before physical_parent)<>task_exited ->
  owned_phase(process_tasks after physical_parent)<>task_exited.
Proof. intros OP LIVE;destruct OP;try exact LIVE;discriminate. Qed.

Lemma launch_parent_operation_tracer before event after:
  launch_operation physical_parent before event after ->
  owned_tracer(process_tasks after physical_child)=owned_tracer(process_tasks before physical_child).
Proof. intro OP;destruct OP;reflexivity. Qed.

Lemma launch_parent_namespace_task before event after:
  namespace_kernel_event before(namespace_process event)after ->namespace_task after=namespace_task before.
Proof. intro STEP;inversion STEP;subst;reflexivity. Qed.

Lemma launch_file_final_view groups actor before namespace events after final:
  LaunchFileRecording groups actor before namespace events after final ->SourceFileView groups after actor final.
Proof. intro RUN;induction RUN;assumption. Qed.

Lemma launch_file_initial_view groups actor before namespace events after final:
  LaunchFileRecording groups actor before namespace events after final ->SourceFileView groups before actor namespace.
Proof. intro RUN;inversion RUN;assumption. Qed.

Definition launch_parent_tick program ordinal namespace_id child_table before namespace event middle:=
  source_recording_tick launch_recording_owner program ordinal
    (launch_parent_context before namespace_id)(launch_parent_context middle namespace_id)before
    (namespace_process event)(launch_parent_tables namespace child_table).

Inductive ParentRecording groups(program namespace_id:nat)(child_table:DescriptorTable):
    nat->NamespaceWorld->ProcessWorld->list process_event->list LeanCage_Entry_CallerPhysical_Tick->
    NamespaceWorld->ProcessWorld->Prop:=
| parent_recording_done:forall ordinal namespace world,
    ParentRecording groups program namespace_id child_table ordinal namespace world[][]namespace world
| parent_recording_next:forall ordinal namespace before event next middle events ticks after_namespace after_world,
    let snapshot:={|source_process_before:=before;source_process_after:=middle;
      source_namespace_before:=namespace;source_namespace_after:=next|}in
    let tick:=launch_parent_tick program ordinal namespace_id child_table before namespace event middle in
    SourcePrimitive launch_operation groups launch_recording_child launch_recording_owner(namespace_process event)tick snapshot ->
    SourceParentView before(physical_identity_task launch_recording_owner)(launch_parent_context before namespace_id) ->
    SourceParentView middle(physical_identity_task launch_recording_owner)(launch_parent_context middle namespace_id) ->
    ParentRecording groups program namespace_id child_table(S ordinal)next middle events ticks after_namespace after_world ->
    ParentRecording groups program namespace_id child_table ordinal namespace before(event::events)(tick::ticks)
      after_namespace after_world.

Theorem parent_recording_owned groups program namespace_id child_table ordinal namespace world events ticks
    after_namespace after_world:
  ParentRecording groups program namespace_id child_table ordinal namespace world events ticks after_namespace after_world ->
  OwnedProgramRecording launch_operation groups launch_recording_child launch_recording_owner program ordinal
    namespace world events ticks after_namespace after_world.
Proof.
  intro RUN;induction RUN;[constructor|].
  eapply owned_program_next with(snapshot:=snapshot);[reflexivity|exact H|exact H0|exact H1|exact IHRUN].
Qed.

Theorem launch_parent_recording groups before namespace events after final:
  LaunchFileRecording groups physical_parent before namespace events after final ->
  namespace_task namespace=physical_parent ->launch_nonnegative_table(namespace_table namespace) ->
  owned_tracer(process_tasks before physical_child)=Some physical_parent ->
  owned_phase(process_tasks before physical_parent)<>task_exited ->
  forall(program ordinal namespace_id:nat)(child_table:DescriptorTable),
  exists ticks,ParentRecording groups program namespace_id child_table ordinal namespace before events ticks final after.
Proof.
  intro RUN;induction RUN;intros TASK VALID TRACER LIVE program ordinal namespace_id child_table.
  - exists[];constructor.
  - assert(NEXT_TASK:namespace_task next=physical_parent).
    { rewrite(launch_parent_namespace_task _ _ _ H1);exact TASK. }
    assert(NEXT_VALID:launch_nonnegative_table(namespace_table next)).
    { eapply launch_namespace_nonnegative;eassumption. }
    assert(NEXT_TRACER:owned_tracer(process_tasks middle physical_child)=Some physical_parent).
    { rewrite(launch_parent_operation_tracer _ _ _ H0);exact TRACER. }
    assert(NEXT_LIVE:owned_phase(process_tasks middle physical_parent)<>task_exited).
    { eapply launch_parent_operation_live;eassumption. }
    destruct(IHRUN NEXT_TASK NEXT_VALID NEXT_TRACER NEXT_LIVE program(S ordinal)namespace_id child_table)
      as[ticks REST].
    eexists;eapply parent_recording_next with(next:=next)(middle:=middle).
    + unfold launch_parent_tick;eapply source_recording_primitive with(snapshot:={|
        source_process_before:=before;source_process_after:=middle;
        source_namespace_before:=namespace;source_namespace_after:=next|}).
      * rewrite launch_recording_owner_task;exact TASK.
      * rewrite launch_recording_owner_task;exact LIVE.
      * apply launch_parent_context_view;exact TRACER.
      * apply launch_parent_context_view;exact NEXT_TRACER.
      * exact H1.
      * intros original SAME;inversion SAME;subst original;rewrite launch_recording_owner_task;exact H0.
      * apply launch_parent_table_here.
      * exact VALID.
      * rewrite launch_recording_owner_task;exact H.
      * rewrite launch_recording_owner_task;eapply launch_file_initial_view;exact RUN.
    + apply launch_parent_context_live;exact LIVE.
    + apply launch_parent_context_live;exact NEXT_LIVE.
    + exact REST.
Qed.

Lemma launch_passive_parent_action world event:
  launch_passive event=true ->source_recording_action launch_recording_owner world(namespace_process event)=
    LeanCage_Entry_CallerPhysical_Action_idle.
Proof.
  intro PASSIVE;destruct event;try reflexivity;try discriminate.
  repeat match goal with
  |H:launch_passive(process_entry(entry_library(original_event ?original)))=true|-_=>is_var original;
    destruct original;try reflexivity;try discriminate
  |H:launch_passive(process_entry(entry_library ?library))=true|-_=>is_var library;
    destruct library;try reflexivity;try discriminate
  |H:launch_passive(process_entry ?entry)=true|-_=>is_var entry;
    destruct entry;try reflexivity;try discriminate
  end.
Qed.

Lemma launch_parent_io_action files tracer phase options group request bytes error:
  source_recording_action launch_recording_owner(launch_world files tracer phase options group)
    (namespace_process(process_machine_event(io_step request(transfer bytes error))))=
  match IO.operation request with
  |reading=>LeanCage_Entry_CallerPhysical_Action_idle
  |writing=>match files physical_parent(IO.descriptor request)with
    |None=>LeanCage_Entry_CallerPhysical_Action_idle
    |Some assigned=>LeanCage_Entry_CallerPhysical_Action_placement(Nat_of_nat assigned)end end.
Proof.
  unfold source_recording_action;cbn[process_machine_event namespace_socket_io process_socket_io source_socket_request].
  rewrite launch_recording_owner_task;reflexivity.
Qed.

Theorem launch_parent_operation_step mayTrace before event after namespace:
  launch_operation physical_parent before event after ->
  LeanCage_Entry_CallerPhysical_Step mayTrace launch_recording_owner launch_recording_child
    (launch_parent_context before namespace)
    (source_recording_action launch_recording_owner before(namespace_process event))
    (launch_parent_context after namespace).
Proof.
  intro OP;destruct OP.
  - rewrite launch_passive_parent_action by exact H;constructor.
  - destruct reply.
    + rewrite launch_parent_io_action,H;destruct(IO.operation q);constructor.
    + constructor.
    + constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - rewrite launch_parent_io_action,H0,H;constructor.
  - change(LeanCage_Entry_CallerPhysical_Step mayTrace launch_recording_owner launch_recording_child
      (source_recording_context launch_recording_owner true task_traced_stop Int64.zero namespace group)
      (LeanCage_Entry_CallerPhysical_Action_request launch_recording_owner(caller_request_nat(Int.repr 16896))
        (caller_options_nat(Int64.repr 1048592)))
      (source_recording_context launch_recording_owner true task_traced_stop(Int64.repr 1048592)namespace group)).
    constructor;constructor.
  - change(LeanCage_Entry_CallerPhysical_Step mayTrace launch_recording_owner launch_recording_child
      (source_recording_context launch_recording_owner true task_traced_stop(Int64.repr 1048592)namespace group)
      (LeanCage_Entry_CallerPhysical_Action_request launch_recording_owner(caller_request_nat(Int.repr 7))
        (caller_options_nat Int64.zero))
      (source_recording_context launch_recording_owner true task_running(Int64.repr 1048592)namespace group)).
    econstructor;[constructor|constructor|left;constructor].
  - constructor.
Qed.

Inductive ParentSupervisorAction:LeanCage_Entry_CallerPhysical_Action->Prop:=
| parent_action_idle:ParentSupervisorAction LeanCage_Entry_CallerPhysical_Action_idle
| parent_action_request:forall actor request options,
    ParentSupervisorAction(LeanCage_Entry_CallerPhysical_Action_request actor request options)
| parent_action_placement:forall group,ParentSupervisorAction(LeanCage_Entry_CallerPhysical_Action_placement group).

Lemma launch_parent_action_profile actor world event:
  ParentSupervisorAction(source_recording_action actor world event).
Proof.
  unfold source_recording_action;destruct event;cbn;try constructor.
  all: repeat match goal with
    | |-context[match ?value with _=>_ end]=>destruct value
    end;constructor.
Qed.

Lemma parent_action_not_native action:
  ParentSupervisorAction action ->Not(Lean.eq action LeanCage_Entry_CallerPhysical_Action_native).
Proof. intro PROFILE;inversion PROFILE;intro SAME;inversion SAME. Qed.

Lemma parent_action_not_traceMe action:
  ParentSupervisorAction action ->Not(Lean.eq action LeanCage_Entry_CallerPhysical_Action_traceMe).
Proof. intro PROFILE;inversion PROFILE;intro SAME;inversion SAME. Qed.

Lemma launch_parent_recorded_step mayTrace program ordinal namespace_id child_table before namespace event middle next groups:
  SourcePrimitive launch_operation groups launch_recording_child launch_recording_owner(namespace_process event)
    (launch_parent_tick program ordinal namespace_id child_table before namespace event middle)
    {|source_process_before:=before;source_process_after:=middle;
      source_namespace_before:=namespace;source_namespace_after:=next|} ->
  LeanCage_Entry_CallerPhysical_Step mayTrace launch_recording_owner launch_recording_child
    (launch_parent_context before namespace_id)
    (source_recording_action launch_recording_owner before(namespace_process event))
    (launch_parent_context middle namespace_id).
Proof.
  intro PRIMITIVE;apply launch_parent_operation_step.
  pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE event(Logic.eq_refl _))as OP.
  rewrite launch_recording_owner_task in OP;exact OP.
Qed.

Lemma launch_recording_offset_succ index:
  ProcessImport.Nat_add(Nat_of_nat index)(Nat_of_nat 1)=Nat_of_nat(S index).
Proof. reflexivity. Qed.

Lemma launch_recorded_source_tick runs run actor program ordinal before after world event tables mayTrace child:
  nth_error runs program=Some run ->source_actor run=actor ->
  nth_error(source_events run)ordinal=Some event ->
  SourceTick runs mayTrace child(source_recording_tick actor program ordinal before after world event tables).
Proof.
  intros PROGRAM ACTOR EVENT.
  pose proof(launch_recorded_source_io runs run actor program ordinal before after world event tables PROGRAM ACTOR EVENT)as IO.
  destruct event;try solve[apply source_tick_idle;reflexivity].
  destruct event;try solve[apply source_tick_idle;reflexivity].
  - destruct(namespace_socket_io(namespace_process(process_entry event)))as[io|]eqn:SOCKET.
    + destruct(IO.operation(source_socket_request io))eqn:OPERATION.
      { apply source_tick_idle;change(source_recording_action actor world(namespace_process(process_entry event))=
          LeanCage_Entry_CallerPhysical_Action_idle).
        unfold source_recording_action;rewrite SOCKET,OPERATION;reflexivity. }
      destruct(process_cgroup_files world(physical_identity_task actor)(IO.descriptor(source_socket_request io)))as[group|]eqn:GROUP.
      * eapply source_tick_placement with(group:=Nat_of_nat group)(actor:=actor)(fd:=caller_request_nat(descriptor(source_socket_request io)))
          (bytes:=journal_byte_values(source_socket_bytes io))(lost:=journal_lost_value(source_socket_lost io)).
        -- apply IO;cbn[ProcessImport.socket source_recording_tick].
           unfold source_recording_socket;rewrite SOCKET,OPERATION;reflexivity.
        -- change(source_recording_action actor world(namespace_process(process_entry event))=
             LeanCage_Entry_CallerPhysical_Action_placement(Nat_of_nat group)).
           unfold source_recording_action;rewrite SOCKET,OPERATION,GROUP;reflexivity.
      * apply source_tick_idle;change(source_recording_action actor world(namespace_process(process_entry event))=
          LeanCage_Entry_CallerPhysical_Action_idle).
        unfold source_recording_action;rewrite SOCKET,OPERATION,GROUP;reflexivity.
    + apply source_tick_idle;change(source_recording_action actor world(namespace_process(process_entry event))=
        LeanCage_Entry_CallerPhysical_Action_idle).
      unfold source_recording_action;rewrite SOCKET;reflexivity.
  - eapply source_tick_returned with(run:=run)(instance:=program)(ordinal:=ordinal).
    + exact PROGRAM.
    + exact EVENT.
    + rewrite ACTOR;reflexivity.
    + reflexivity.
  - eapply source_tick_lost with(run:=run)(instance:=program)(ordinal:=ordinal).
    + exact PROGRAM.
    + exact EVENT.
    + rewrite ACTOR;reflexivity.
    + reflexivity.
Qed.

Theorem parent_recording_journal groups program namespace_id child_table ordinal namespace world events ticks
    after_namespace after_world:
  ParentRecording groups program namespace_id child_table ordinal namespace world events ticks after_namespace after_world ->
  forall runs run mayTrace prefix suffix,
    nth_error runs program=Some run ->source_actor run=launch_recording_owner ->
    source_events run=prefix++map namespace_process events++suffix ->length prefix=ordinal ->
  RecordedRun runs mayTrace launch_recording_owner launch_recording_child
    (launch_parent_context world namespace_id)ticks(launch_parent_context after_world namespace_id).
Proof.
  intro RUN;induction RUN;intros runs run mayTrace prefix suffix PROGRAM ACTOR EVENTS LENGTH.
  - constructor.
  - assert(EVENT:nth_error(source_events run)ordinal=Some(namespace_process event)).
    { rewrite <-LENGTH,EVENTS;apply recording_head_event. }
    eapply recorded_next with(tick:=tick).
    + unfold launch_parent_tick;eapply launch_recorded_source_tick;eassumption.
    + eapply launch_parent_recorded_step;exact H.
    + change(RecordedRun runs mayTrace launch_recording_owner launch_recording_child
        (launch_parent_context middle namespace_id)ticks(launch_parent_context after_world namespace_id)).
      eapply IHRUN with(prefix:=prefix++[namespace_process event])(suffix:=suffix);try eassumption.
      * rewrite EVENTS;cbn[map];repeat rewrite <-app_assoc;reflexivity.
      * rewrite length_app;cbn;lia.
Qed.

Theorem parent_recording_supervisor_slice groups program namespace_id child_table ordinal namespace world events ticks
    after_namespace after_world:
  ParentRecording groups program namespace_id child_table ordinal namespace world events ticks after_namespace after_world ->
  forall mayTrace prefix suffix,
  LeanCage_Entry_CallerWitness_SupervisorSlice mayTrace launch_recording_owner launch_recording_child
    (tick_values(prefix++ticks++suffix))(Nat_of_nat(length prefix))(launch_parent_context world namespace_id)
    (Nat_of_nat(length prefix+length ticks))(launch_parent_context after_world namespace_id).
Proof.
  intro RUN;induction RUN;intros mayTrace prefix suffix.
  - rewrite app_nil_l,length_nil,Nat.add_0_r;constructor.
  - assert(SELECTED:nth_error(prefix++tick::ticks++suffix)(length prefix)=Some tick).
    { rewrite nth_error_app2 by lia;rewrite Nat.sub_diag;reflexivity. }
    pose proof(IHRUN mayTrace(prefix++[tick])suffix)as REST.
    assert(SAME:(prefix++[tick])++ticks++suffix=prefix++(tick::ticks)++suffix).
    { repeat rewrite <-app_assoc;reflexivity. }
    rewrite SAME,length_app in REST;cbn[length]in REST.
    eapply LeanCage_Entry_CallerWitness_SupervisorSlice_next with(tick:=tick).
    + exact(actual_tick_position _ _ _ SELECTED).
    + constructor.
    + eapply launch_parent_recorded_step;exact H.
    + apply parent_action_not_native,launch_parent_action_profile.
    + apply parent_action_not_traceMe,launch_parent_action_profile.
    + rewrite launch_recording_offset_succ.
      replace(S(length prefix))with(length prefix+1)%nat by lia.
      replace(length prefix+length(tick::ticks))%nat with(length prefix+1+length ticks)%nat by(cbn;lia).
      exact REST.
Qed.
