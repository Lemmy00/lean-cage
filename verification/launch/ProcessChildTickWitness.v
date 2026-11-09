(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Sample the same actual child source operations before worker entry. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffAllocation.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessSourceWorlds ProcessLaunchWitness ProcessLaunchRecordingWitness
  ProcessParentRecordingWitness ProcessChildRecordingWitness ProcessCapabilityRecording.
From EntryProcess Require Import ProcessCallerConnection.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceWorldTrace NamespacePhysical
  NamespaceDescriptorFrame NamespaceForkWorldWitness NamespaceChildWorldWitness NamespacePaths NamespaceGuestFlags NamespaceCapabilities.
From EntryNamespace Require Import NamespaceSocket.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Lemma launch_recording_child_key:
  nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child)=2%nat.
Proof.
  rewrite <-physical_identity_task_key,launch_recording_child_task.
  change((0*Z.to_nat 2147483648+2)%nat=2%nat);reflexivity.
Qed.

Definition launch_child_context(world:ProcessWorld)(namespace:nat):=
  source_recording_context launch_recording_owner false
    (owned_phase(process_tasks world physical_child))(owned_options(process_tasks world physical_child))
    namespace(owned_cgroup(process_tasks world physical_child)).

Definition launch_child_tables(namespace:NamespaceWorld)(parent:DescriptorTable)(key:nat):DescriptorTable:=
  if Nat.eqb key 1 then parent
  else if Nat.eqb key 2 then namespace_table namespace
  else if Nat.eqb key 3 then fork_fixture_other else fun _=>None.

Lemma launch_child_table_here namespace child:
  launch_child_tables namespace child
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child))=namespace_table namespace.
Proof. rewrite launch_recording_child_key;reflexivity. Qed.

Lemma launch_child_context_view world namespace:
  owned_tracer(process_tasks world physical_child)=None ->
  SourceProcessView world(physical_identity_task launch_recording_child)(launch_child_context world namespace).
Proof.
  intro TRACER;unfold launch_child_context;apply source_recording_context_view;
    rewrite launch_recording_child_task;try reflexivity.
  exact TRACER.
Qed.

Lemma launch_child_context_live world namespace:
  owned_phase(process_tasks world physical_child)<>task_exited ->
  SourceParentView world(physical_identity_task launch_recording_child)(launch_child_context world namespace).
Proof.
  intro LIVE;unfold launch_child_context;apply source_recording_parent_view.
  rewrite launch_recording_child_task;exact LIVE.
Qed.

Lemma launch_child_operation_live before event after:
  launch_operation physical_child before event after ->
  owned_phase(process_tasks before physical_child)<>task_exited ->
  owned_phase(process_tasks after physical_child)<>task_exited.
Proof. intros OP LIVE;destruct OP;try exact LIVE;discriminate. Qed.

Lemma launch_child_operation_tracer before event after:
  launch_operation physical_child before event after ->
  owned_tracer(process_tasks after physical_child)=owned_tracer(process_tasks before physical_child).
Proof. intro OP;destruct OP;reflexivity. Qed.

Lemma launch_child_namespace_task before event after:
  namespace_kernel_event before(namespace_process event)after ->namespace_task after=namespace_task before.
Proof. intro STEP;inversion STEP;subst;reflexivity. Qed.

Definition launch_child_tick program ordinal namespace_id parent_table before namespace event middle:=
  source_recording_tick launch_recording_child program ordinal
    (launch_child_context before namespace_id)(launch_child_context middle namespace_id)before
    (namespace_process event)(launch_child_tables namespace parent_table).

Inductive ChildRecording groups(program namespace_id:nat)(parent_table:DescriptorTable):
    nat->NamespaceWorld->ProcessWorld->list process_event->list LeanCage_Entry_CallerPhysical_Tick->
    NamespaceWorld->ProcessWorld->Prop:=
| child_recording_done:forall ordinal namespace world,
    ChildRecording groups program namespace_id parent_table ordinal namespace world[][]namespace world
| child_recording_next:forall ordinal namespace before event next middle events ticks after_namespace after_world,
    let snapshot:={|source_process_before:=before;source_process_after:=middle;
      source_namespace_before:=namespace;source_namespace_after:=next|}in
    let tick:=launch_child_tick program ordinal namespace_id parent_table before namespace event middle in
    SourcePrimitive launch_operation groups launch_recording_child launch_recording_child(namespace_process event)tick snapshot ->
    SourceParentView before(physical_identity_task launch_recording_child)(launch_child_context before namespace_id) ->
    SourceParentView middle(physical_identity_task launch_recording_child)(launch_child_context middle namespace_id) ->
    ChildRecording groups program namespace_id parent_table(S ordinal)next middle events ticks after_namespace after_world ->
    ChildRecording groups program namespace_id parent_table ordinal namespace before(event::events)(tick::ticks)
      after_namespace after_world.

Theorem child_recording_owned groups program namespace_id parent_table ordinal namespace world events ticks
    after_namespace after_world:
  ChildRecording groups program namespace_id parent_table ordinal namespace world events ticks after_namespace after_world ->
  OwnedProgramRecording launch_operation groups launch_recording_child launch_recording_child program ordinal
    namespace world events ticks after_namespace after_world.
Proof.
  intro RUN;induction RUN;[constructor|].
  eapply owned_program_next with(snapshot:=snapshot);[reflexivity|exact H|exact H0|exact H1|exact IHRUN].
Qed.

Theorem launch_child_recording groups before namespace events after final:
  LaunchFileRecording groups physical_child before namespace events after final ->
  namespace_task namespace=physical_child ->launch_nonnegative_table(namespace_table namespace) ->
  owned_tracer(process_tasks before physical_child)=None ->
  owned_phase(process_tasks before physical_child)<>task_exited ->
  forall(program ordinal namespace_id:nat)(parent_table:DescriptorTable),
  exists ticks,ChildRecording groups program namespace_id parent_table ordinal namespace before events ticks final after.
Proof.
  intro RUN;induction RUN;intros TASK VALID TRACER LIVE program ordinal namespace_id parent_table.
  - exists[];constructor.
  - assert(NEXT_TASK:namespace_task next=physical_child).
    { rewrite(launch_child_namespace_task _ _ _ H1);exact TASK. }
    assert(NEXT_VALID:launch_nonnegative_table(namespace_table next)).
    { eapply launch_namespace_nonnegative;eassumption. }
    assert(NEXT_TRACER:owned_tracer(process_tasks middle physical_child)=None).
    { rewrite(launch_child_operation_tracer _ _ _ H0);exact TRACER. }
    assert(NEXT_LIVE:owned_phase(process_tasks middle physical_child)<>task_exited).
    { eapply launch_child_operation_live;eassumption. }
    destruct(IHRUN NEXT_TASK NEXT_VALID NEXT_TRACER NEXT_LIVE program(S ordinal)namespace_id parent_table)
      as[ticks REST].
    eexists;eapply child_recording_next with(next:=next)(middle:=middle).
    + unfold launch_child_tick;eapply source_recording_primitive with(snapshot:={|
        source_process_before:=before;source_process_after:=middle;
        source_namespace_before:=namespace;source_namespace_after:=next|}).
      * rewrite launch_recording_child_task;exact TASK.
      * rewrite launch_recording_child_task;exact LIVE.
      * apply launch_child_context_view;exact TRACER.
      * apply launch_child_context_view;exact NEXT_TRACER.
      * exact H1.
      * intros original SAME;inversion SAME;subst original;rewrite launch_recording_child_task;exact H0.
      * apply launch_child_table_here.
      * exact VALID.
      * rewrite launch_recording_child_task;exact H.
      * rewrite launch_recording_child_task;eapply launch_file_initial_view;exact RUN.
    + apply launch_child_context_live;exact LIVE.
    + apply launch_child_context_live;exact NEXT_LIVE.
    + exact REST.
Qed.

Lemma launch_passive_child_action world event:
  launch_passive event=true ->source_recording_action launch_recording_child world(namespace_process event)=
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

Lemma launch_child_io_action files tracer phase options group request bytes error:
  source_recording_action launch_recording_child(launch_world files tracer phase options group)
    (namespace_process(process_machine_event(io_step request(transfer bytes error))))=
  match IO.operation request with
  |reading=>LeanCage_Entry_CallerPhysical_Action_idle
  |writing=>match files physical_child(IO.descriptor request)with
    |None=>LeanCage_Entry_CallerPhysical_Action_idle
    |Some assigned=>LeanCage_Entry_CallerPhysical_Action_placement(Nat_of_nat assigned)end end.
Proof.
  unfold source_recording_action;cbn[process_machine_event namespace_socket_io process_socket_io source_socket_request].
  rewrite launch_recording_child_task;reflexivity.
Qed.

Theorem launch_child_operation_step mayTrace before event after namespace:
  launch_operation physical_child before event after ->
  LeanCage_Entry_CallerPhysical_Step mayTrace launch_recording_owner launch_recording_child
    (launch_child_context before namespace)
    (source_recording_action launch_recording_child before(namespace_process event))
    (launch_child_context after namespace).
Proof.
  intro OP;destruct OP.
  - rewrite launch_passive_child_action by exact H;constructor.
  - destruct reply.
    + rewrite launch_child_io_action,H;destruct(IO.operation q);constructor.
    + constructor.
    + constructor.
  - constructor.
  - constructor.
  - constructor.
  - discriminate H.
  - rewrite launch_child_io_action,H0,H;constructor.
  - discriminate H.
  - discriminate H.
  - constructor.
Qed.

Lemma launch_child_recorded_step mayTrace program ordinal namespace_id parent_table before namespace event middle next groups:
  SourcePrimitive launch_operation groups launch_recording_child launch_recording_child(namespace_process event)
    (launch_child_tick program ordinal namespace_id parent_table before namespace event middle)
    {|source_process_before:=before;source_process_after:=middle;
      source_namespace_before:=namespace;source_namespace_after:=next|} ->
  LeanCage_Entry_CallerPhysical_Step mayTrace launch_recording_owner launch_recording_child
    (launch_child_context before namespace_id)
    (source_recording_action launch_recording_child before(namespace_process event))
    (launch_child_context middle namespace_id).
Proof.
  intro PRIMITIVE;apply launch_child_operation_step.
  pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE event(Logic.eq_refl _))as OP.
  rewrite launch_recording_child_task in OP;exact OP.
Qed.

Theorem child_recording_journal groups program namespace_id parent_table ordinal namespace world events ticks
    after_namespace after_world:
  ChildRecording groups program namespace_id parent_table ordinal namespace world events ticks after_namespace after_world ->
  forall runs run mayTrace prefix suffix,
    nth_error runs program=Some run ->source_actor run=launch_recording_child ->
    source_events run=prefix++map namespace_process events++suffix ->length prefix=ordinal ->
  RecordedRun runs mayTrace launch_recording_owner launch_recording_child
    (launch_child_context world namespace_id)ticks(launch_child_context after_world namespace_id).
Proof.
  intro RUN;induction RUN;intros runs run mayTrace prefix suffix PROGRAM ACTOR EVENTS LENGTH.
  - constructor.
  - assert(EVENT:nth_error(source_events run)ordinal=Some(namespace_process event)).
    { rewrite <-LENGTH,EVENTS;apply recording_head_event. }
    eapply recorded_next with(tick:=tick).
    + unfold launch_child_tick;eapply launch_recorded_source_tick;eassumption.
    + eapply launch_child_recorded_step;exact H.
    + change(RecordedRun runs mayTrace launch_recording_owner launch_recording_child
        (launch_child_context middle namespace_id)ticks(launch_child_context after_world namespace_id)).
      eapply IHRUN with(prefix:=prefix++[namespace_process event])(suffix:=suffix);try eassumption.
      * rewrite EVENTS;cbn[map];repeat rewrite <-app_assoc;reflexivity.
      * rewrite length_app;cbn;lia.
Qed.


Definition child_useful_namespace_events b prefix:=
  (repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3)++
  map namespace_guest_event(prefix++[entry_image
    (Vptr(NativeHandoffArguments.handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
    (Vptr(NativeHandoffAllocation.handoff_arguments b)Ptrofs.zero)
    (Vptr(NativeHandoffAllocation.handoff_environment b)Ptrofs.zero)]).

Theorem actual_same_fork_child_ticks cell command source memory pair parameters k
    branch_memory b after caller prefix world namespace_id:
  namespace_useful_child_image_fields cell command source memory pair parameters k
    branch_memory b after caller prefix world ->
  exists originals final ticks,
    child_useful_namespace_events b prefix=map namespace_process originals /\
    namespace_table final=fork_fixture_worker_table /\
    ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0
      child_fork_namespace(launch_world launch_fork_files None task_running Int64.zero None)originals ticks
      final(launch_world launch_parent_files None task_running Int64.zero None).
Proof.
  intro FIELDS.
  destruct(actual_same_fork_child_file_recording _ _ _ _ _ _ _ _ _ _ _ _ _ FIELDS)
    as[originals[final[EVENTS[RECORDING TABLE]]]].
  assert(TASK:namespace_task child_fork_namespace=physical_child)by reflexivity.
  assert(VALID:launch_nonnegative_table(namespace_table child_fork_namespace)).
  { exact launch_actual_fork_nonnegative. }
  destruct(launch_child_recording _ _ _ _ _ _ RECORDING TASK VALID(Logic.eq_refl _)
    ltac:(discriminate)1 0 namespace_id(namespace_table fork_fixture_world))as[ticks RUN].
  exists originals,final,ticks;split;[exact EVENTS|];split;assumption.
Qed.

Lemma child_recording_ambient_nonnegative:launch_nonnegative_table fork_fixture_other.
Proof.
  intros fd binding PRESENT;unfold fork_fixture_other in PRESENT.
  destruct(Z.leb 0(Int.signed fd)&&Z.leb(Int.signed fd)2)eqn:BOUNDS;[|discriminate].
  apply andb_true_iff in BOUNDS as[LOW HIGH];apply Z.leb_le;exact LOW.
Qed.

Lemma child_recording_tables_nonnegative namespace parent:
  launch_nonnegative_table parent ->launch_nonnegative_table(namespace_table namespace) ->
  forall actor,launch_nonnegative_table(launch_child_tables namespace parent actor).
Proof.
  intros PARENT CHILD actor;unfold launch_child_tables;destruct(Nat.eqb actor 1);[exact PARENT|].
  destruct(Nat.eqb actor 2);[exact CHILD|].
  destruct(Nat.eqb actor 3);[exact child_recording_ambient_nonnegative|intros;discriminate].
Qed.

Definition child_recording_capabilities parent namespace:CapabilityWorld:={|
  capability_tables:=launch_child_tables namespace parent;capability_messages:=[]|}.

Lemma child_recording_tick_observed program ordinal namespace_id parent namespace world event after:
  launch_nonnegative_table parent ->launch_nonnegative_table(namespace_table namespace) ->
  CapabilityObserved(launch_child_tick program ordinal namespace_id parent world namespace event after)
    (child_recording_capabilities parent namespace).
Proof.
  intros PARENT CHILD actor fd;unfold launch_child_tick,child_recording_capabilities;cbn[capability_tables].
  symmetry;apply source_recording_table;apply child_recording_tables_nonnegative;assumption.
Qed.

Lemma child_recording_primitive_nonnegative program ordinal namespace_id parent namespace world event next after groups:
  SourcePrimitive launch_operation groups launch_recording_child launch_recording_child(namespace_process event)
    (launch_child_tick program ordinal namespace_id parent world namespace event after)
    {|source_process_before:=world;source_process_after:=after;
      source_namespace_before:=namespace;source_namespace_after:=next|} ->
  launch_nonnegative_table(namespace_table namespace).
Proof.
  intros PRIMITIVE fd binding PRESENT.
  rewrite <-(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE)in PRESENT.
  unfold physical_tick_table in PRESENT;destruct(Z.leb 0(Int.signed fd))eqn:LOW;
    [apply Z.leb_le;exact LOW|discriminate].
Qed.

Lemma child_recording_capabilities_retable parent namespace next:
  capability_retable(child_recording_capabilities parent namespace)2(namespace_table next)=
    child_recording_capabilities parent next.
Proof.
  unfold capability_retable,child_recording_capabilities;f_equal;apply functional_extensionality;intro actor.
  unfold task_table_put;destruct(Nat.eqb actor 2)eqn:CHILD.
  - apply Nat.eqb_eq in CHILD;subst actor;reflexivity.
  - cbn[capability_tables];unfold launch_child_tables;rewrite CHILD;reflexivity.
Qed.

Theorem child_recording_capability_history groups program namespace_id parent ordinal namespace world events ticks
    after_namespace after_world:
  ChildRecording groups program namespace_id parent ordinal namespace world events ticks after_namespace after_world ->
  launch_nonnegative_table parent ->
  forall runs run prefix suffix native metadata external can_acquire,
    nth_error runs program=Some run ->source_actor run=launch_recording_child ->
    source_events run=prefix++map namespace_process events++suffix ->length prefix=ordinal ->
  CapabilityHistory launch_operation groups runs native metadata external can_acquire
    launch_recording_owner launch_recording_child(child_recording_capabilities parent namespace)ticks
    (child_recording_capabilities parent after_namespace).
Proof.
  intro RUN;induction RUN;intros PARENT runs run prefix suffix native metadata external can_acquire PROGRAM ACTOR EVENTS LENGTH.
  - constructor.
  - assert(EVENT:nth_error(source_events run)ordinal=Some(namespace_process event)).
    { rewrite <-LENGTH,EVENTS;apply recording_head_event. }
    assert(OBSERVED:CapabilityObserved tick(child_recording_capabilities parent namespace)).
    { unfold tick;apply child_recording_tick_observed;[exact PARENT|].
      eapply child_recording_primitive_nonnegative;exact H. }
    assert(AFTER:capability_pending
      (capability_retable (child_recording_capabilities parent namespace)
        (nat_of_Nat (LeanCage_Entry_CallerPhysical_taskKey (source_actor run)))
        (namespace_table next)) [] = child_recording_capabilities parent next).
    { rewrite ACTOR,launch_recording_child_key,child_recording_capabilities_retable;reflexivity. }
    eapply capability_history_next with(middle:=child_recording_capabilities parent next);[exact OBSERVED| |].
    + apply recorded_capability_source;eapply source_capability_call with(run:=run)(program:=program)
        (ordinal:=ordinal)(event:=namespace_process event)(retained:=[])(snapshot:=snapshot).
      * exact PROGRAM.
      * exact EVENT.
      * reflexivity.
      * rewrite ACTOR;exact H.
      * reflexivity.
      * exact OBSERVED.
      * apply incl_refl.
      * symmetry;exact AFTER.
    + eapply IHRUN with(run:=run)(prefix:=prefix++[namespace_process event])(suffix:=suffix);try eassumption.
      * rewrite EVENTS;cbn[map];repeat rewrite <-app_assoc;reflexivity.
      * rewrite length_app;cbn;lia.
Qed.
