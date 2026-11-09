(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Record the actual source branches without inventing source ordinals. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller ProcessJournal ProcessImport ProcessSourceRecording
  ProcessSourceTables ProcessSourceWorlds ProcessCallerConnection ProcessOwnership ProcessSourceOrigin.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespacePhysical NamespacePaths
  NamespaceHandles NamespaceSocket.
Import ListNotations.
Local Close Scope lean_scope.

Definition actual_caller_source_run actor cell before events after
    (started:caller_source_machine before)(executed:namespace_steps caller_ge cell before events after):CallerSourceRun:=
  {|source_actor:=actor;source_cell:=cell;source_before:=before;source_events:=events;source_after:=after;
    source_started:=started;source_executed:=executed|}.

(* Every source event has its own genuine primitive snapshot and source ref.
   The namespaces on consecutive snapshots are the same actual table chain. *)
Inductive ProgramRecording
    (primitive:LeanCage_Entry_ProcessIdentity->namespace_event->
      LeanCage_Entry_CallerPhysical_Tick->SourceSnapshot->Prop)
    (actor:LeanCage_Entry_ProcessIdentity)(program:nat):
    nat->NamespaceWorld->list namespace_event->list LeanCage_Entry_CallerPhysical_Tick->NamespaceWorld->Prop:=
| program_recording_done:forall ordinal world,ProgramRecording primitive actor program ordinal world[][]world
| program_recording_next:forall ordinal event tick snapshot events ticks after,
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    primitive actor event tick snapshot ->
    ProgramRecording primitive actor program(S ordinal)(source_namespace_after snapshot)events ticks after ->
    ProgramRecording primitive actor program ordinal(source_namespace_before snapshot)(event::events)(tick::ticks)after.

Lemma recording_cursor_here cursor program:source_cursor_next cursor program program=S(cursor program).
Proof. unfold source_cursor_next;rewrite Nat.eqb_refl;reflexivity. Qed.
Lemma recording_cursor_other cursor program query:query<>program ->
  source_cursor_next cursor program query=cursor query.
Proof.
  intro OTHER;unfold source_cursor_next;assert(NE:Nat.eqb query program=false)by(apply Nat.eqb_neq;exact OTHER).
  rewrite NE;reflexivity.
Qed.
Lemma recording_world_here worlds program after:source_world_next worlds program after program=after.
Proof. unfold source_world_next;rewrite Nat.eqb_refl;reflexivity. Qed.
Lemma recording_world_other worlds program after query:query<>program ->
  source_world_next worlds program after query=worlds query.
Proof.
  intro OTHER;unfold source_world_next;assert(NE:Nat.eqb query program=false)by(apply Nat.eqb_neq;exact OTHER).
  rewrite NE;reflexivity.
Qed.

Lemma recording_head_event(A:Type)(prefix:list A)event events suffix:
  nth_error(prefix++event::events++suffix)(length prefix)=Some event.
Proof. rewrite nth_error_app2 by lia;rewrite Nat.sub_diag;reflexivity. Qed.

Theorem program_recording_tables primitive actor program ordinal first events ticks after:
  ProgramRecording primitive actor program ordinal first events ticks after ->
  forall runs run prefix suffix cursor worlds,
    nth_error runs program=Some run ->source_actor run=actor ->
    source_events run=prefix++events++suffix ->length prefix=ordinal ->cursor program=ordinal ->worlds program=first ->
    exists final final_worlds,
      SourceTableSchedule primitive runs cursor worlds ticks final final_worlds /\
      final program=(ordinal+length events)%nat /\final_worlds program=after /\
      forall query,query<>program ->final query=cursor query /\final_worlds query=worlds query.
Proof.
  intro RECORDING;induction RECORDING;intros runs run prefix suffix cursor worlds PROGRAM ACTOR EVENTS LENGTH CURSOR WORLD.
  - exists cursor,worlds;split;[constructor|]. split;[cbn;lia|]. split;[exact WORLD|intros;auto].
  - assert(EVENT:nth_error(source_events run)(cursor program)=Some event).
    { rewrite CURSOR,<-LENGTH,EVENTS;apply recording_head_event. }
    assert(REST:source_events run=(prefix++[event])++events++suffix).
    { rewrite EVENTS;repeat rewrite <-app_assoc;reflexivity. }
    destruct(IHRECORDING runs run(prefix++[event])suffix(source_cursor_next cursor program)
      (source_world_next worlds program(source_namespace_after snapshot))PROGRAM ACTOR REST)
      as[final[final_worlds[TAIL[FINAL[AFTER FRAME]]]]].
    + rewrite length_app;cbn;lia.
    + rewrite recording_cursor_here,CURSOR;reflexivity.
    + apply recording_world_here.
    + exists final,final_worlds;split.
      * econstructor;[eapply source_table_next with(run:=run)(event:=event)(snapshot:=snapshot)|exact TAIL].
        -- exact PROGRAM.
        -- exact EVENT.
        -- rewrite CURSOR;exact H.
        -- rewrite ACTOR;exact H0.
        -- symmetry;exact WORLD.
      * split;[cbn;lia|]. split;[exact AFTER|].
        intros query OTHER;destruct(FRAME _ OTHER)as[POSITION TABLE].
        rewrite recording_cursor_other in POSITION by exact OTHER.
        rewrite recording_world_other in TABLE by exact OTHER;auto.
Qed.

(* Process snapshots retain the same parent liveness projection, including
   before/after states of the actual close and options operations. *)
Inductive OwnedProgramRecording operation groups child owner program:
    nat->NamespaceWorld->ProcessOwnership.ProcessWorld->list process_event->
    list LeanCage_Entry_CallerPhysical_Tick->NamespaceWorld->ProcessOwnership.ProcessWorld->Prop:=
| owned_program_done:forall ordinal namespace world,
    OwnedProgramRecording operation groups child owner program ordinal namespace world[][]namespace world
| owned_program_next:forall ordinal event tick snapshot events ticks after_namespace after_world,
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    SourcePrimitive operation groups child owner(namespace_process event)tick snapshot ->
    SourceParentView(source_process_before snapshot)(physical_identity_task owner)
      (LeanCage_Entry_CallerPhysical_Tick_before tick) ->
    SourceParentView(source_process_after snapshot)(physical_identity_task owner)
      (LeanCage_Entry_CallerPhysical_Tick_after tick) ->
    OwnedProgramRecording operation groups child owner program(S ordinal)(source_namespace_after snapshot)
      (source_process_after snapshot)events ticks after_namespace after_world ->
    OwnedProgramRecording operation groups child owner program ordinal(source_namespace_before snapshot)
      (source_process_before snapshot)(event::events)(tick::ticks)after_namespace after_world.

Theorem owned_program_recording_namespaces operation groups child owner program ordinal namespace world events ticks
    after_namespace after_world:
  OwnedProgramRecording operation groups child owner program ordinal namespace world events ticks after_namespace after_world ->
  ProgramRecording(SourcePrimitive operation groups child)owner program ordinal namespace(map namespace_process events)
    ticks after_namespace.
Proof. intro RECORDING;induction RECORDING;cbn;[constructor|econstructor;eassumption]. Qed.

Theorem owned_program_recording_processes operation groups child owner program ordinal namespace world events ticks
    after_namespace after_world:
  OwnedProgramRecording operation groups child owner program ordinal namespace world events ticks after_namespace after_world ->
  forall runs run prefix suffix cursor worlds other,
    nth_error runs program=Some run ->source_actor run=owner ->
    source_events run=prefix++map namespace_process events++suffix ->length prefix=ordinal ->
    cursor program=ordinal ->worlds program=namespace ->
    exists final final_worlds,
      SourceProcessSchedule operation groups child runs program other cursor worlds world ticks final final_worlds after_world /\
      final program=(ordinal+length events)%nat /\final_worlds program=after_namespace /\
      forall query,query<>program ->final query=cursor query /\final_worlds query=worlds query.
Proof.
  intro RECORDING;induction RECORDING;intros runs run prefix suffix cursor worlds other PROGRAM ACTOR EVENTS LENGTH CURSOR WORLD.
  - exists cursor,worlds;split;[constructor|]. split;[cbn;lia|]. split;[exact WORLD|intros;auto].
  - assert(EVENT:nth_error(source_events run)(cursor program)=Some(namespace_process event)).
    { rewrite CURSOR,<-LENGTH,EVENTS;apply recording_head_event. }
    assert(REST:source_events run=(prefix++[namespace_process event])++map namespace_process events++suffix).
    { rewrite EVENTS;cbn[map];repeat rewrite <-app_assoc;reflexivity. }
    destruct(IHRECORDING runs run(prefix++[namespace_process event])suffix(source_cursor_next cursor program)
      (source_world_next worlds program(source_namespace_after snapshot))other PROGRAM ACTOR REST)
      as[final[final_worlds[TAIL[FINAL[AFTER FRAME]]]]].
    + rewrite length_app;cbn;lia.
    + rewrite recording_cursor_here,CURSOR;reflexivity.
    + apply recording_world_here.
    + exists final,final_worlds;split.
      * econstructor;[eapply source_process_parent with(run:=run)(original:=event)(snapshot:=snapshot)|exact TAIL].
        -- exact PROGRAM.
        -- exact EVENT.
        -- rewrite CURSOR;exact H.
        -- rewrite ACTOR;exact H0.
        -- symmetry;exact WORLD.
        -- rewrite ACTOR;exact H1.
        -- rewrite ACTOR;exact H2.
      * split;[cbn;lia|]. split;[exact AFTER|].
        intros query OTHER;destruct(FRAME _ OTHER)as[POSITION TABLE].
        rewrite recording_cursor_other in POSITION by exact OTHER.
        rewrite recording_world_other in TABLE by exact OTHER;auto.
Qed.

Record ActualForkCallerRuns owner child cell root child_return parent_after child_after
    common parent_tail child_tail returned:Type:={
  fork_parent_run:CallerSourceRun;
  fork_child_run:CallerSourceRun;
  fork_parent_actor:source_actor fork_parent_run=owner;
  fork_child_actor:source_actor fork_child_run=child;
  fork_parent_cell:source_cell fork_parent_run=cell;
  fork_child_cell:source_cell fork_child_run=cell;
  fork_parent_before:source_before fork_parent_run=root;
  fork_child_before:source_before fork_child_run=child_return;
  fork_parent_events:source_events fork_parent_run=common++namespace_forked returned::parent_tail;
  fork_child_events:source_events fork_child_run=child_tail;
  fork_parent_after:source_after fork_parent_run=parent_after;
  fork_child_after:source_after fork_child_run=child_after;
  fork_programs_distinct:NoDup(map source_actor[fork_parent_run;fork_child_run]);
  fork_parent_program:SourceProgramOwner[fork_parent_run;fork_child_run]owner 0;
  fork_child_program:SourceProgramOwner[fork_parent_run;fork_child_run]child 1
}.

(* The parent retains the full prepared-root program. The child's C stream
   starts at its actual zero return, whose source invariant is obtained from
   that same common prefix and fork. Its consumed source cursor is therefore
   zero, while the parent's is length common + 1. *)
Definition actual_fork_caller_runs owner child cell root common fork_call parent_return child_return
    parent_tail parent_after child_tail child_after returned
    (different:owner<>child)(started:caller_source_machine root)
    (shared:namespace_steps caller_ge cell root common fork_call)
    (parent_fork:namespace_step caller_ge cell fork_call(namespace_forked returned)parent_return)
    (child_fork:namespace_step caller_ge cell fork_call(namespace_forked Int.zero)child_return)
    (parent_source:namespace_steps caller_ge cell parent_return parent_tail parent_after)
    (child_source:namespace_steps caller_ge cell child_return child_tail child_after):
    ActualForkCallerRuns owner child cell root child_return parent_after child_after common parent_tail child_tail returned.
Proof.
  assert(PARENT:namespace_steps caller_ge cell root(common++namespace_forked returned::parent_tail)parent_after).
  { eapply namespace_steps_append;[exact shared|econstructor;[exact parent_fork|exact parent_source]]. }
  assert(CHILD_STARTED:caller_source_machine child_return).
  { eapply caller_source_namespace_step;[eapply caller_source_namespace_prefix;[exact started|exact shared]|exact child_fork]. }
  set(parent:=actual_caller_source_run owner cell root(common++namespace_forked returned::parent_tail)parent_after started PARENT).
  set(branch:=actual_caller_source_run child cell child_return child_tail child_after CHILD_STARTED child_source).
  assert(UNIQUE:NoDup(map source_actor[parent;branch])).
  { change(NoDup[owner;child]);constructor.
    - cbn;intros[SAME|IMPOSSIBLE];[congruence|exact IMPOSSIBLE].
    - constructor;[cbn;tauto|constructor]. }
  refine{|fork_parent_run:=parent;fork_child_run:=branch;fork_programs_distinct:=UNIQUE|};try reflexivity.
  - eapply source_distinct_tasks_own_program;[exact UNIQUE|reflexivity|reflexivity].
  - eapply source_distinct_tasks_own_program;[exact UNIQUE|reflexivity|reflexivity].
Defined.

Definition source_recording_socket actor event:=match namespace_socket_io event with
  |None=>LeanCage_Entry_CallerPhysical_SocketObservation_none
  |Some io=>match IO.operation(source_socket_request io)with
    |reading=>LeanCage_Entry_CallerPhysical_SocketObservation_read actor
      (caller_request_nat(descriptor(source_socket_request io)))
      (Nat_of_nat(Z.to_nat(requested(source_socket_request io))))(journal_byte_values(source_socket_bytes io))
    |writing=>LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor
      (caller_request_nat(descriptor(source_socket_request io)))
      (journal_byte_values(source_socket_bytes io))(journal_lost_value(source_socket_lost io))end end.

Definition source_recording_action actor world event:=match event with
  |namespace_process(process_traced request _ _ data _)|
   namespace_process(process_trace_lost request _ _ data)=>
    LeanCage_Entry_CallerPhysical_Action_request actor(caller_request_nat request)(caller_options_nat(caller_payload_word data))
  |_=>match namespace_socket_io event with
    |None=>LeanCage_Entry_CallerPhysical_Action_idle
    |Some io=>match IO.operation(source_socket_request io)with
      |reading=>LeanCage_Entry_CallerPhysical_Action_idle
      |writing=>match process_cgroup_files world(physical_identity_task actor)(descriptor(source_socket_request io))with
        |None=>LeanCage_Entry_CallerPhysical_Action_idle
        |Some group=>LeanCage_Entry_CallerPhysical_Action_placement(Nat_of_nat group)end end end end.

Definition source_recording_tick actor program ordinal before after world event(tables:nat->DescriptorTable):=
  LeanCage_Entry_CallerPhysical_Tick_mk before(source_recording_action actor world event)after
    (fun key fd=>physical_objects(tables(nat_of_Nat key))fd)
    (fun key fd=>physical_cloexec(tables(nat_of_Nat key))fd)
    (source_recording_socket actor event)(source_reference program ordinal)
    (ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_PrimitiveLabel).

Theorem source_recording_table actor program ordinal before after world event tables key fd:
  (forall binding,tables key fd=Some binding ->(0<=Int.signed fd)%Z) ->
  physical_tick_table(source_recording_tick actor program ordinal before after world event tables)key fd=tables key fd.
Proof.
  intro VALID_TABLE;unfold physical_tick_table,source_recording_tick;cbn.
  rewrite nat2Natid.
  destruct(Z.leb 0(Int.signed fd))eqn:VALID.
  - apply Z.leb_le in VALID;destruct(native_descriptor_number_valid _ VALID)as[BOUND NUMBER].
    unfold physical_objects,physical_cloexec;rewrite BOUND,NUMBER.
    destruct(tables key fd)as[binding|]eqn:PRESENT;[|reflexivity].
    rewrite native_descriptor_object_exact,physical_object_code_exact.
    destruct binding as[object flag];cbn[physical_flag physical_bool];destruct flag;reflexivity.
  - destruct(tables key fd)as[binding|]eqn:PRESENT;[|reflexivity].
    pose proof(VALID_TABLE _(Logic.eq_refl _))as NONNEGATIVE;apply Z.leb_gt in VALID;lia.
Qed.

Theorem source_recording_primitive operation groups child actor program ordinal snapshot before after event tables:
  namespace_task(source_namespace_before snapshot)=physical_identity_task actor ->
  owned_phase(process_tasks(source_process_before snapshot)(physical_identity_task actor))<>task_exited ->
  SourceProcessView(source_process_before snapshot)(physical_identity_task child)before ->
  SourceProcessView(source_process_after snapshot)(physical_identity_task child)after ->
  namespace_kernel_event(source_namespace_before snapshot)event(source_namespace_after snapshot) ->
  (forall original,event=namespace_process original ->operation(physical_identity_task actor)
    (source_process_before snapshot)original(source_process_after snapshot)) ->
  tables(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))=namespace_table(source_namespace_before snapshot) ->
  (forall fd binding,namespace_table(source_namespace_before snapshot)fd=Some binding ->(0<=Int.signed fd)%Z) ->
  SourceFileView groups(source_process_before snapshot)(physical_identity_task actor)(source_namespace_before snapshot) ->
  SourceFileView groups(source_process_after snapshot)(physical_identity_task actor)(source_namespace_after snapshot) ->
  SourcePrimitive operation groups child actor event
    (source_recording_tick actor program ordinal before after(source_process_before snapshot)event tables)snapshot.
Proof.
  intros TASK LIVE BEFORE AFTER KERNEL PROCESS TABLE VALID FILES_BEFORE FILES_AFTER.
  constructor;try assumption.
  - intro fd;rewrite source_recording_table.
    + rewrite TABLE;reflexivity.
    + rewrite TABLE;intro binding;apply VALID.
  - intros request target address data returned EVENT CHILD;subst event;reflexivity.
  - intros request target address data EVENT CHILD;subst event;reflexivity.
  - intros io EVENT WRITING;unfold source_recording_tick;cbn.
    unfold source_recording_socket;rewrite EVENT,WRITING;reflexivity.
  - intros q bytes error group EVENT WRITING FILE CANONICAL;subst event.
    unfold source_recording_tick;cbn;unfold source_recording_action.
    cbn[process_machine_event namespace_socket_io process_socket_io source_socket_request].
    rewrite WRITING,FILE;reflexivity.
  - intros fd reply EVENT;subst event;reflexivity.
  - reflexivity.
Qed.

Definition source_recording_group(group:option nat):ProcessImport.Option_inst1 Lean.Nat:=match group with
  |None=>ProcessImport.Option_none_inst1 Lean.Nat
  |Some assigned=>ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat assigned)end.
Definition source_recording_issued(phase:TaskPhase)(options:int64):List_inst1 Lean.Nat:=
  if Int64.eq options(Int64.repr 1048592)then
    match phase with task_running=>caller_request_values[Int.repr 16896;Int.repr 7]
      |_=>caller_request_values[Int.repr 16896]end
  else caller_request_values[].
Definition source_recording_context(owner:LeanCage_Entry_ProcessIdentity)(traced:bool)
    (phase:TaskPhase)(options:int64)(namespace:nat)(group:option nat):=
  LeanCage_Entry_CallerPhysical_Context_mk
    (if traced then ProcessImport.Option_some_inst1 LeanCage_Entry_ProcessIdentity owner
     else ProcessImport.Option_none_inst1 LeanCage_Entry_ProcessIdentity)
    (caller_options_nat options)(source_recording_issued phase options)
    ProcessImport.Bool_true ProcessImport.Bool_true(Nat_of_nat namespace)(source_recording_group group).

Theorem source_recording_context_view world child owner(traced:bool)phase options namespace group:
  owned_tracer(process_tasks world child)=
    (if traced then Some(physical_identity_task owner)else None) ->
  owned_options(process_tasks world child)=options ->owned_cgroup(process_tasks world child)=group ->
  SourceProcessView world child(source_recording_context owner traced phase options namespace group).
Proof.
  intros TRACER OPTIONS GROUP;constructor.
  - rewrite GROUP;unfold source_context_group,source_recording_context,source_recording_group;cbn.
    destruct group;[rewrite nat2Natid|];reflexivity.
  - rewrite TRACER;unfold source_context_tracer,source_recording_context;destruct traced;reflexivity.
  - rewrite OPTIONS;unfold source_recording_context,caller_options_nat;cbn;rewrite nat2Natid;reflexivity.
Qed.

Theorem source_recording_parent_view world parent owner traced phase options namespace group:
  owned_phase(process_tasks world parent)<>task_exited ->
  SourceParentView world parent(source_recording_context owner traced phase options namespace group).
Proof.
  intro LIVE;unfold SourceParentView,source_recording_context;cbn;split;[intro EXITED;contradiction|discriminate].
Qed.
