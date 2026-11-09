(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Execute the useful grant queue on the same actual source ticks. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine LibraryPreservation ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffTraceEvents.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness ProcessPhysicalTrace
  ProcessSourceRecording ProcessLaunchWitness ProcessLaunchRecordingWitness ProcessParentRecordingWitness
  ProcessChildTickWitness ProcessChildOtherWitness ProcessDescriptor ProcessPaths ProcessGlobalCalls ProcessPlacement ProcessReleaseWitness ProcessClock ProcessStructure ProcessAllocation.
From EntryReporting Require Import ResultLayout SenderSource.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceWorldTrace NamespacePhysical
  NamespaceHandles NamespaceChannel NamespaceSocket NamespaceSocketTick NamespaceDescriptorFrame NamespaceForkWorldWitness
  NamespaceLaunchWitness NamespaceParentWitness NamespaceClosure NamespacePreparedFork NamespacePaths NamespaceCaller.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Local Opaque launch_recording_owner launch_recording_child.

Lemma queue_execution_append channel before prefix middle suffix after:
  physical_queue_execution channel before prefix middle ->physical_queue_execution channel middle suffix after ->
  physical_queue_execution channel before(prefix++suffix)after.
Proof. intro FIRST;induction FIRST;intro LAST;[exact LAST|cbn;econstructor;eauto]. Qed.

Lemma queue_socket_none channel tick buffers:
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_none ->
  physical_queue_operation channel tick buffers buffers.
Proof. intro NONE;unfold physical_queue_operation,physical_tick_projection;rewrite NONE;cbn;constructor. Qed.

Lemma queue_sockets_none channel ticks buffers:
  Forall(fun tick=>ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_none)ticks ->
  physical_queue_execution channel buffers ticks buffers.
Proof. intro NONE;induction NONE;[constructor|econstructor;[apply queue_socket_none;exact H|exact IHNONE]]. Qed.

Theorem queue_child_recording_frames groups program namespace_id parent ordinal namespace world events ticks final after:
  ChildRecording groups program namespace_id parent ordinal namespace world events ticks final after ->
  Forall(fun event=>namespace_socket_io(namespace_process event)=None)events ->
  forall channel buffers,physical_queue_execution channel buffers ticks buffers.
Proof.
  intro RUN;induction RUN;intros QUIET channel buffers;[constructor|].
  inversion QUIET as[|original tail HEAD TAIL];subst original tail.
  econstructor;[apply queue_socket_none|apply IHRUN;exact TAIL].
  change(source_recording_socket launch_recording_child(namespace_process event)=
    LeanCage_Entry_CallerPhysical_SocketObservation_none).
  unfold source_recording_socket;rewrite HEAD;reflexivity.
Qed.

Lemma queue_enqueue_empty buffers actor:
  channel_enqueue buffers actor parent_endpoint[]=buffers.
Proof. destruct buffers;cbn[channel_enqueue channel_tag];rewrite app_nil_r;reflexivity. Qed.
Lemma queue_enqueue_append buffers actor first second:
  channel_enqueue(channel_enqueue buffers actor parent_endpoint first)actor parent_endpoint second=
    channel_enqueue buffers actor parent_endpoint(first++second).
Proof. destruct buffers;unfold channel_enqueue;cbn;f_equal;unfold channel_tag;rewrite map_app,app_assoc;reflexivity. Qed.

Lemma queue_read_grant tick actor binding:
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_read actor
    (native_descriptor_number(Int.repr 60))(Nat_of_nat 1)physical_grant_bytes ->
  physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))(Int.repr 60)=Some binding ->
  descriptor_object binding=release_endpoint 60 child_endpoint ->
  physical_queue_operation 60 tick(channel_enqueue channel_empty 1 parent_endpoint[Byte.repr 165])channel_empty.
Proof.
  intros SOCKET PRESENT OBJECT.
  pose proof(physical_tick_read_projection 60 tick actor(Int.repr 60)1 physical_grant_bytes binding SOCKET
    ltac:(reflexivity)ltac:(change(0<=60);lia)PRESENT OBJECT)as PROJECT.
  unfold physical_queue_operation;rewrite PROJECT;cbn[Datatypes.snd].
  change(channel_operation(physical_tick_table tick)60
    (channel_enqueue channel_empty 1 parent_endpoint[Byte.repr 165])
    (channel_read(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))(Int.repr 60)1[Byte.repr 165])channel_empty).
  eapply channel_read_step with(side:=child_endpoint)(count:=1%nat);[exists binding;auto|lia].
Qed.

Definition queue_parent_slots(table:DescriptorTable):Prop:=forall fd binding side,
  table fd=Some binding ->descriptor_object binding=release_endpoint 60 side ->
  fd=Int.repr 9\/fd=Int.repr 60.
Definition queue_parent_peer(table:DescriptorTable):Prop:=exists binding,
  table(Int.repr 9)=Some binding /\descriptor_object binding=release_endpoint 60 parent_endpoint.
Definition queue_parent_profile(original:process_event):Prop:=
  process_nonreaping original=true /\
  (forall fd reply,original=process_entry(entry_library(close_returned fd reply)) ->fd<>Int.repr 9) /\
  forall io,namespace_socket_io(namespace_process original)=Some io ->
    IO.operation(source_socket_request io)=writing /\
    (descriptor(source_socket_request io)=Int.repr 7\/
      descriptor(source_socket_request io)=Int.repr 8\/descriptor(source_socket_request io)=Int.repr 9).
Definition queue_parent_bytes(original:process_event):list Byte.int:=
  match namespace_socket_io(namespace_process original)with
  |None=>[]|Some io=>if Int.eq(descriptor(source_socket_request io))(Int.repr 9)then source_socket_bytes io else[]end.
Definition queue_parent_payload events:=flat_map queue_parent_bytes events.

Lemma queue_parent_slots_frame before after:
  descriptor_object_frame before after ->queue_parent_slots before ->queue_parent_slots after.
Proof.
  intros FRAME SLOTS fd binding side PRESENT OBJECT;destruct(FRAME _ _ PRESENT)as[previous[OLD SAME]].
  eapply SLOTS with(side:=side);[exact OLD|congruence].
Qed.

Lemma queue_parent_peer_flags table fd flag:
  queue_parent_peer table ->queue_parent_peer(descriptor_flags table fd flag).
Proof.
  intros[binding[PRESENT OBJECT]];unfold queue_parent_peer,descriptor_flags;rewrite PRESENT.
  destruct(Int.eq(Int.repr 9)fd).
  - eexists;split;[reflexivity|exact OBJECT].
  - exists binding;split;[reflexivity|exact OBJECT].
Qed.

Lemma queue_parent_peer_step before original after:
  namespace_kernel_event before(namespace_process original)after ->queue_parent_profile original ->
  queue_parent_peer(namespace_table before) ->queue_parent_peer(namespace_table after).
Proof.
  intros KERNEL[NONREAP[NOCLOSE IO]]PEER;inversion KERNEL;subst;try exact PEER;
    cbn[process_nonreaping]in NONREAP;try discriminate.
  - assert(OTHER:descriptor<>Int.repr 9)by(eapply NOCLOSE;reflexivity).
    destruct PEER as[binding[PRESENT OBJECT]];
      match goal with CLOSE:close_table _ _ _ _|-_=>inversion CLOSE;subst end;try solve[exists binding;auto].
    all:exists binding;cbn[namespace_retable namespace_table];unfold table_remove;
      rewrite Int.eq_false by congruence;auto.
  - apply queue_parent_peer_flags;exact PEER.
  - apply queue_parent_peer_flags;exact PEER.
Qed.

Lemma queue_fork_parent_slots:queue_parent_slots(namespace_table fork_fixture_world).
Proof.
  intros fd binding side PRESENT OBJECT;change(fork_fixture_inherited fd=Some binding)in PRESENT.
  unfold fork_fixture_inherited,fork_fixture_duplicated,fork_fixture_paired,table_remove,table_put in PRESENT.
  destruct(Int.eq fd(Int.repr 10));[discriminate|].
  destruct(Int.eq fd(Int.repr 60))eqn:SIXTY;[right;apply Int.same_if_eq;exact SIXTY|].
  destruct(Int.eq fd(Int.repr 9))eqn:NINE;[left;apply Int.same_if_eq;exact NINE|].
  unfold fork_fixture_ordinary in PRESENT;destruct(Z.leb 0(Int.signed fd)&&Z.leb(Int.signed fd)8);[|discriminate].
  inversion PRESENT;subst binding;discriminate.
Qed.
Lemma queue_fork_parent_peer:queue_parent_peer(namespace_table fork_fixture_world).
Proof. exists(endpoint_binding 60 parent_endpoint);split;reflexivity. Qed.

Lemma queue_select_outside tables actor channel fd event:
  (0<=Int.signed fd)%Z ->
  (forall binding side,tables actor fd=Some binding ->descriptor_object binding<>release_endpoint channel side) ->
  physical_select tables actor channel(native_descriptor_number fd)event=channel_passed.
Proof.
  intros NONNEGATIVE OUTSIDE;destruct(native_descriptor_number_valid fd NONNEGATIVE)as[BOUND NUMBER].
  unfold physical_select,physical_descriptor;rewrite BOUND,NUMBER.
  destruct(tables actor fd)as[binding|]eqn:PRESENT;[|reflexivity].
  destruct(descriptor_object binding)as[object|actual side]eqn:OBJECT;[reflexivity|].
  destruct(Nat.eqb actual channel)eqn:SAME;[|reflexivity].
  apply Nat.eqb_eq in SAME;subst actual;exfalso;exact(OUTSIDE binding side(Logic.eq_refl _)OBJECT).
Qed.

Lemma queue_parent_io_fd io:
  (descriptor(source_socket_request io)=Int.repr 7\/
    descriptor(source_socket_request io)=Int.repr 8\/descriptor(source_socket_request io)=Int.repr 9) ->
  (0<=Int.signed(descriptor(source_socket_request io)))%Z.
Proof. intros[FD|[FD|FD]];rewrite FD;change(0<=7) || change(0<=8) || change(0<=9);lia. Qed.

Lemma queue_parent_one_operation groups program ordinal namespace_id child_table namespace world event middle next
    buffers
    (primitive:SourcePrimitive launch_operation groups launch_recording_child launch_recording_owner(namespace_process event)
      (launch_parent_tick program ordinal namespace_id child_table world namespace event middle)
      {|source_process_before:=world;source_process_after:=middle;
        source_namespace_before:=namespace;source_namespace_after:=next|}):
  queue_parent_profile event ->queue_parent_slots(namespace_table namespace) ->queue_parent_peer(namespace_table namespace) ->
  physical_queue_operation 60(launch_parent_tick program ordinal namespace_id child_table world namespace event middle)
    buffers(channel_enqueue buffers 1 parent_endpoint(queue_parent_bytes event)).
Proof.
  intros PROFILE SLOTS PEER.
  destruct(namespace_socket_io(namespace_process event))as[io|]eqn:SOCKET.
  - destruct(proj2(proj2 PROFILE)io SOCKET)as[WRITING FD].
    assert(OBSERVED:ProcessImport.socket(launch_parent_tick program ordinal namespace_id child_table world namespace event middle)=
      LeanCage_Entry_CallerPhysical_SocketObservation_wrote launch_recording_owner
        (native_descriptor_number(descriptor(source_socket_request io)))(source_socket_values(source_socket_bytes io))
        (physical_flag(source_socket_lost io))).
    { change(source_recording_socket launch_recording_owner(namespace_process event)=
        LeanCage_Entry_CallerPhysical_SocketObservation_wrote launch_recording_owner
          (native_descriptor_number(descriptor(source_socket_request io)))(source_socket_values(source_socket_bytes io))
          (physical_flag(source_socket_lost io))).
      unfold source_recording_socket;rewrite SOCKET,WRITING;reflexivity. }
    unfold queue_parent_bytes;rewrite SOCKET.
    destruct(Int.eq(descriptor(source_socket_request io))(Int.repr 9))eqn:SELECTED.
    + apply Int.same_if_eq in SELECTED.
      destruct PEER as[binding[PRESENT OBJECT]].
      assert(BINDING:physical_tick_table(launch_parent_tick program ordinal namespace_id child_table world namespace event middle)
        (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner))
        (descriptor(source_socket_request io))=Some binding).
      { rewrite(source_primitive_table _ _ _ _ _ _ _ primitive),SELECTED;exact PRESENT. }
      pose proof(physical_tick_write_projection 60 _ launch_recording_owner _ _ _ binding parent_endpoint OBSERVED
        (source_socket_values_valid _)(queue_parent_io_fd _ FD)BINDING OBJECT)as PROJECT.
      unfold physical_queue_operation;rewrite PROJECT;cbn[Datatypes.snd].
      rewrite source_socket_values_exact,launch_recording_owner_key.
      apply channel_write_step;exists binding;split.
      * rewrite launch_recording_owner_key in BINDING;exact BINDING.
      * exact OBJECT.
    + rewrite queue_enqueue_empty;unfold physical_queue_operation,physical_tick_projection.
      rewrite OBSERVED,source_socket_values_valid;cbn beta iota zeta.
      rewrite(queue_select_outside _ _ _ _ _ (queue_parent_io_fd _ FD));[constructor|].
      intros binding side BINDING OBJECT.
      rewrite(source_primitive_table _ _ _ _ _ _ _ primitive)in BINDING.
      destruct(SLOTS _ _ _ BINDING OBJECT)as[NINE|SIXTY].
      * rewrite NINE,Int.eq_true in SELECTED;discriminate.
      * destruct FD as[FD|[FD|FD]];rewrite FD in SIXTY;vm_compute in SIXTY;discriminate.
  - unfold queue_parent_bytes;rewrite SOCKET,queue_enqueue_empty;apply queue_socket_none.
    change(source_recording_socket launch_recording_owner(namespace_process event)=
      LeanCage_Entry_CallerPhysical_SocketObservation_none).
    unfold source_recording_socket;rewrite SOCKET;reflexivity.
Qed.

Theorem queue_parent_recording_execution groups program namespace_id child_table ordinal namespace world events ticks final after:
  ParentRecording groups program namespace_id child_table ordinal namespace world events ticks final after ->
  Forall queue_parent_profile events ->queue_parent_slots(namespace_table namespace) ->queue_parent_peer(namespace_table namespace) ->
  forall buffers,physical_queue_execution 60 buffers ticks
    (channel_enqueue buffers 1 parent_endpoint(queue_parent_payload events)) /\queue_parent_peer(namespace_table final).
Proof.
  intro RUN;induction RUN;intros PROFILE SLOTS PEER buffers.
  - split;[cbn[queue_parent_payload flat_map];rewrite queue_enqueue_empty;constructor|exact PEER].
  - inversion PROFILE as[|original tail HEAD TAIL];subst original tail.
    assert(KERNEL:namespace_kernel_event namespace(namespace_process event)next)
      by(exact(source_primitive_namespace _ _ _ _ _ _ _ H)).
    assert(NEXT_SLOTS:queue_parent_slots(namespace_table next)).
    { eapply queue_parent_slots_frame;[eapply namespace_process_object_frame;exact KERNEL|exact SLOTS]. }
    assert(NEXT_PEER:queue_parent_peer(namespace_table next))by(eapply queue_parent_peer_step;eassumption).
    destruct(IHRUN TAIL NEXT_SLOTS NEXT_PEER(channel_enqueue buffers 1 parent_endpoint(queue_parent_bytes event)))as[REST LAST].
    split;[|exact LAST].
    change(physical_queue_execution 60 buffers(tick::ticks)
      (channel_enqueue buffers 1 parent_endpoint(queue_parent_bytes event++queue_parent_payload events))).
    rewrite <-queue_enqueue_append;econstructor;[|exact REST].
    eapply queue_parent_one_operation;[exact H|exact HEAD|exact SLOTS|exact PEER].
Qed.

Lemma queue_sender_excludes_read:
  ~closure_function descriptor_calls
    (External(io_function reading)[tint;tptr tvoid;tulong]tlong cc_default).
Proof.
  intros[id[MEMBER LOOKUP]];unfold descriptor_calls in MEMBER;cbn in MEMBER.
  repeat destruct MEMBER as[MEMBER|MEMBER];try contradiction;subst id;vm_compute in LOOKUP;discriminate.
Qed.
Lemma queue_sender_excludes_close:~closure_function descriptor_calls close_definition.
Proof.
  intros[id[MEMBER LOOKUP]];unfold descriptor_calls in MEMBER;cbn in MEMBER.
  repeat destruct MEMBER as[MEMBER|MEMBER];try contradiction;subst id;vm_compute in LOOKUP;discriminate.
Qed.

Lemma queue_sender_io_writes fd cell state request:
  descriptor_machine fd(live state) ->boundary cell state request ->operation request=writing.
Proof.
  intros GOOD IO;inversion IO;subst state;subst q.
  destruct(operation request)eqn:OP;[|reflexivity].
  exfalso;apply queue_sender_excludes_read.
  destruct GOOD as[[GLOBAL[FUNCTION CONT]]CONTROL];exact FUNCTION.
Qed.

Lemma queue_live_library_nonreap ge cell before event after:
  library_step ge cell(live before)event(live after) ->
  process_nonreaping(process_entry(entry_library event))=true.
Proof.
  intro STEP;inversion STEP;subst;try reflexivity.
  match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>inversion ORIGINAL;subst;reflexivity end.
Qed.

Lemma queue_sender_io_profile fd cell before event after io:
  descriptor_machine fd(live before) ->library_step caller_ge cell(live before)event(live after) ->
  namespace_socket_io(namespace_process(process_entry(entry_library event)))=Some io ->
  operation(source_socket_request io)=writing /\descriptor(source_socket_request io)=fd.
Proof.
  intros GOOD STEP SOCKET.
  pose proof(descriptor_library_event_checked _ _ _ _ _ GOOD STEP)as DESCRIPTOR.
  destruct event;cbn[namespace_socket_io process_socket_io]in SOCKET;try discriminate.
  destruct ev;cbn[process_socket_io]in SOCKET;try discriminate.
  - destruct r;try discriminate;inversion SOCKET;subst io;cbn[source_socket_request].
    assert(WRITING:operation q=writing).
    { inversion STEP;subst.
      match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>inversion ORIGINAL;subst end.
      eapply queue_sender_io_writes;[exact GOOD|eassumption]. }
    split;[exact WRITING|apply DESCRIPTOR;exact WRITING].
  - inversion STEP;subst.
    match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>inversion ORIGINAL end.
Qed.

Lemma queue_sender_step_profile cell before event after:
  descriptor_machine(Int.repr 8)(live before) ->library_step caller_ge cell(live before)event(live after) ->
  queue_parent_profile(process_entry(entry_library event)) /\queue_parent_bytes(process_entry(entry_library event))=[].
Proof.
  intros GOOD STEP;split.
  - split;[eapply queue_live_library_nonreap;exact STEP|]. split.
    + intros fd reply SAME;inversion SAME;subst;inversion STEP;subst.
      exfalso;apply queue_sender_excludes_close;destruct GOOD as[[GLOBAL[FUNCTION CONT]]CONTROL];exact FUNCTION.
    + intros io SOCKET;destruct(queue_sender_io_profile _ _ _ _ _ _ GOOD STEP SOCKET)as[WRITING FD].
      split;[exact WRITING|right;left;exact FD].
  - unfold queue_parent_bytes;destruct(namespace_socket_io(namespace_process(process_entry(entry_library event))))as[io|]eqn:SOCKET;
      [|reflexivity].
    destruct(queue_sender_io_profile _ _ _ _ _ _ GOOD STEP SOCKET)as[WRITING FD];rewrite FD;reflexivity.
Qed.

Lemma queue_result_environment:result_ge=caller_ge.
Proof. reflexivity. Qed.

Theorem queue_actual_sender_profile cell sequence result before events after:
  library_steps result_ge cell(live(sender_initial(Int.repr 8)sequence result 0 Kstop before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  Forall(fun event=>queue_parent_profile(process_entry(entry_library event)) /\
    queue_parent_bytes(process_entry(entry_library event))=[])events.
Proof.
  intro SOURCE;rewrite queue_result_environment in SOURCE.
  assert(INITIAL:descriptor_machine(Int.repr 8)(live(sender_initial(Int.repr 8)sequence result 0 Kstop before))).
  { apply descriptor_initial;[exact descriptor_sender_binding|intro REQUIRED;eexists;reflexivity]. }
  remember(live(sender_initial(Int.repr 8)sequence result 0 Kstop before))as start.
  remember(live(Returnstate(Vint Int.zero)Kstop after))as target.
  clear Heqstart;revert INITIAL after Heqtarget;induction SOURCE;intros INITIAL final TARGET.
  - constructor.
  - destruct s as[first|memory];[|exfalso;eapply library_dead_cannot_resume;exact H].
    destruct mid as[middle|memory].
    + constructor;[eapply queue_sender_step_profile;[exact INITIAL|exact H]|].
      eapply IHSOURCE;[eapply descriptor_library_step;[exact INITIAL|exact H]|exact TARGET].
    + destruct(library_dead_steps _ _ _ _ _ SOURCE)as[EMPTY IMPOSSIBLE];rewrite TARGET in IMPOSSIBLE;discriminate.
Qed.

Lemma queue_passive_nonreap event:launch_passive event=true ->process_nonreaping event=true.
Proof.
  intro PASSIVE;destruct event;cbn[launch_passive]in PASSIVE;
    try discriminate;try solve[unfold process_quiet_event in PASSIVE;apply andb_true_iff in PASSIVE;tauto].
  destruct event;cbn[launch_passive]in PASSIVE;
    try discriminate;try solve[unfold process_quiet_event in PASSIVE;apply andb_true_iff in PASSIVE;tauto].
  destruct event;cbn[launch_passive]in PASSIVE;
    try discriminate;unfold process_quiet_event in PASSIVE;apply andb_true_iff in PASSIVE;tauto.
Qed.

Lemma queue_passive_socket_none event:
  launch_passive event=true ->namespace_socket_io(namespace_process event)=None.
Proof.
  intro PASSIVE;destruct event;cbn[namespace_socket_io process_socket_io];try reflexivity.
  destruct event;cbn[process_socket_io];try reflexivity.
  destruct event;cbn[process_socket_io];try reflexivity.
  destruct ev;cbn[process_socket_io];try reflexivity;discriminate PASSIVE.
Qed.

Lemma queue_parent_passive_profile event:
  launch_passive event=true ->queue_parent_profile event /\queue_parent_bytes event=[].
Proof.
  intro PASSIVE;pose proof(queue_passive_socket_none _ PASSIVE)as SOCKET.
  split.
  - split;[apply queue_passive_nonreap;exact PASSIVE|]. split.
    + intros fd reply SAME;subst event;discriminate PASSIVE.
    + intros io IO;rewrite SOCKET in IO;discriminate.
  - unfold queue_parent_bytes;rewrite SOCKET;reflexivity.
Qed.

Definition queue_namespace_profile event:Prop:=exists original,event=namespace_process original /\queue_parent_profile original.
Definition queue_namespace_bytes event:=match event with
  |namespace_process original=>queue_parent_bytes original|_=>[]end.
Definition queue_namespace_payload events:=flat_map queue_namespace_bytes events.

Lemma queue_source_profile:queue_namespace_profile namespace_source_event.
Proof. exists process_source_event;split;[reflexivity|exact(proj1(queue_parent_passive_profile process_source_event(Logic.eq_refl _)))]. Qed.
Lemma queue_sources_profile count:Forall queue_namespace_profile(repeat namespace_source_event count).
Proof. apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst event;exact queue_source_profile. Qed.
Lemma queue_sources_payload count:queue_namespace_payload(repeat namespace_source_event count)=[].
Proof. induction count;cbn[repeat queue_namespace_payload flat_map queue_namespace_bytes queue_parent_bytes];assumption || reflexivity. Qed.
Lemma queue_namespace_payload_append first second:
  queue_namespace_payload(first++second)=queue_namespace_payload first++queue_namespace_payload second.
Proof. apply flat_map_app. Qed.

Lemma queue_parent_close_profile fd reply:
  fd<>Int.repr 9 ->queue_parent_profile(process_entry(entry_library(close_returned fd reply))).
Proof. intro OTHER;split;[reflexivity|]. split;[intros actual observed SAME;inversion SAME;subst;exact OTHER|intros;discriminate]. Qed.

Lemma queue_prefix_profile events:
  Forall namespace_parent_prefix_event events ->Forall queue_namespace_profile events /\queue_namespace_payload events=[].
Proof.
  intro PROFILE;induction PROFILE;[split;constructor|].
  destruct IHPROFILE as[TAIL EMPTY];split.
  - constructor;[|exact TAIL];destruct H as[SOURCE|[fd[NUMBER CLOSE]]];subst x.
    + exact queue_source_profile.
    + eexists;split;[reflexivity|apply queue_parent_close_profile].
      cbn in NUMBER;repeat destruct NUMBER as[NUMBER|NUMBER];try contradiction;subst fd;vm_compute;discriminate.
  - change(queue_namespace_bytes x++queue_namespace_payload l=[]);rewrite EMPTY,app_nil_r.
    destruct H as[SOURCE|[fd[NUMBER CLOSE]]];subst x;reflexivity.
Qed.

Lemma queue_quiet_profile counts:
  Forall queue_namespace_profile(namespace_quiet_trace counts) /\queue_namespace_payload(namespace_quiet_trace counts)=[].
Proof.
  induction counts as[|count counts IH];[split;constructor|].
  unfold namespace_quiet_trace in *;cbn[flat_map];destruct IH as[PROFILE EMPTY];split.
  - apply Forall_app;split;[apply queue_sources_profile|exact PROFILE].
  - rewrite queue_namespace_payload_append,queue_sources_payload,EMPTY;reflexivity.
Qed.

Lemma queue_namespace_map_payload events:
  queue_namespace_payload(map namespace_process events)=queue_parent_payload events.
Proof.
  induction events as[|event events IH];[reflexivity|].
  change(queue_parent_bytes event++queue_namespace_payload(map namespace_process events)=
    queue_parent_bytes event++queue_parent_payload events).
  rewrite IH;reflexivity.
Qed.

Lemma queue_namespace_map_profiles events:
  Forall queue_namespace_profile(map namespace_process events) ->Forall queue_parent_profile events.
Proof.
  intro PROFILE;induction events;[constructor|].
  inversion PROFILE as[|event rest HEAD TAIL];subst;constructor;[|apply IHevents;exact TAIL].
  destruct HEAD as[original[SAME GOOD]];inversion SAME;subst;exact GOOD.
Qed.

Definition queue_namespace_quiet event:=queue_namespace_profile event /\queue_namespace_bytes event=[].
Lemma queue_namespace_quiet_result events:
  Forall queue_namespace_quiet events ->Forall queue_namespace_profile events /\queue_namespace_payload events=[].
Proof.
  intro EVENTS;induction EVENTS;[split;constructor|].
  destruct H as[PROFILE EMPTY],IHEVENTS as[TAIL REST];split;[constructor;assumption|].
  change(queue_namespace_bytes x++queue_namespace_payload l=[]);rewrite EMPTY,REST;reflexivity.
Qed.
Lemma queue_sources_quiet count:Forall queue_namespace_quiet(repeat namespace_source_event count).
Proof. apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst event;split;[exact queue_source_profile|reflexivity]. Qed.

Ltac queue_known_no_socket:=
  split;
  [eexists;split;[reflexivity|];unfold queue_parent_profile;split;
    [vm_compute;reflexivity|split;[intros;discriminate|intros;discriminate]]|reflexivity].

Lemma queue_admission_profile cell locals status first second:
  Forall queue_namespace_quiet
    (map namespace_process(physical_admission_events cell locals(Int.repr 7)status first second)).
Proof.
  unfold physical_admission_events;repeat(rewrite ?map_app,?map_repeat;cbn[map]).
  repeat first[(apply Forall_app;split)|apply queue_sources_quiet|
    (apply Forall_cons;[queue_known_no_socket|])].
  apply Forall_cons.
  - unfold queue_namespace_quiet;split.
    + eexists;split;[reflexivity|]. unfold queue_parent_profile;split;[reflexivity|]. split.
      * intros fd reply SAME;discriminate.
      * intros io SOCKET;inversion SOCKET;subst io;split;[reflexivity|left;reflexivity].
    + reflexivity.
  - repeat first[(apply Forall_app;split)|apply queue_sources_quiet|
      (apply Forall_cons;[queue_known_no_socket|])|constructor].

Qed.

Lemma queue_close_seven_quiet:queue_namespace_quiet(namespace_close_event(Int.repr 7)(close_ok None)).
Proof. split;[eexists;split;[reflexivity|apply queue_parent_close_profile;vm_compute;discriminate]|reflexivity]. Qed.

Lemma queue_clock_quiet cell before events value after:
  entry_errno_ready cell before ->process_steps admission_ge cell(live(Callstate(Internal f_now_ms)[]Kstop before))events
    (live(Returnstate(Vlong value)Kstop after)) ->
  Forall queue_namespace_quiet(map namespace_process events).
Proof.
  intros READY SOURCE;pose proof(launch_actual_clock_passive _ _ _ _ _ READY SOURCE)as PASSIVE.
  apply Forall_map;eapply Forall_impl;[|exact PASSIVE];intros event GOOD.
  destruct(queue_parent_passive_profile _ GOOD)as[PROFILE EMPTY];split;[eexists;auto|exact EMPTY].
Qed.

Lemma queue_callback_profile cell memory status admission sequence events
    (shape:NamespaceCallbackShape cell memory status admission(Int.repr 8)sequence events):
  Forall queue_namespace_profile events /\queue_namespace_payload events=[].
Proof.
  apply queue_namespace_quiet_result;rewrite(callback_event_order _ _ _ _ _ _ _ shape).
  assert(QUIET:forall counts,Forall queue_namespace_quiet(namespace_quiet_trace counts)).
  { intro counts;unfold namespace_quiet_trace;induction counts;cbn[flat_map];[constructor|].
    apply Forall_app;split;[apply queue_sources_quiet|exact IHcounts]. }
  repeat(apply Forall_app;split);try apply QUIET.
  - apply queue_admission_profile.
  - constructor;[exact queue_close_seven_quiet|constructor].
  - eapply queue_clock_quiet;[exact(callback_clock_ready _ _ _ _ _ _ _ shape)|exact(callback_clock_source _ _ _ _ _ _ _ shape)].
  - apply Forall_map.
    pose proof(queue_actual_sender_profile _ _ _ _ _ _ (callback_sender_source _ _ _ _ _ _ _ shape))as PROFILE.
    eapply Forall_impl;[|exact PROFILE];intros event[GOOD EMPTY];split;[|exact EMPTY].
    exists(process_entry(entry_library event));split;[reflexivity|exact GOOD].
Qed.

Lemma queue_release_profile request:
  descriptor request=Int.repr 9 ->operation request=writing ->
  Forall queue_namespace_profile(map namespace_process(release_useful_events(Int.repr 2)request)) /\
  queue_namespace_payload(map namespace_process(release_useful_events(Int.repr 2)request))=[Byte.repr 165].
Proof.
  intros FD WRITING;unfold release_useful_events;repeat(rewrite ?map_app,?map_repeat;cbn[map]);split.
  - repeat first[(apply Forall_app;split)|apply queue_sources_profile|
      (apply Forall_cons;[eexists;split;[reflexivity|];unfold queue_parent_profile;split;
        [reflexivity|split;[intros;discriminate|intros;discriminate]]|])].
    apply Forall_cons.
    + eexists;split;[reflexivity|];unfold queue_parent_profile;split;[reflexivity|]. split.
      * intros;discriminate.
      * intros io SOCKET;inversion SOCKET;subst io;split;[exact WRITING|right;right;exact FD].
    + repeat first[(apply Forall_app;split)|apply queue_sources_profile|
        (apply Forall_cons;[eexists;split;[reflexivity|];unfold queue_parent_profile;split;
          [reflexivity|split;[intros;discriminate|intros;discriminate]]|])|constructor].
  - cbn[app map queue_namespace_payload flat_map repeat queue_namespace_bytes queue_parent_bytes namespace_socket_io process_socket_io
      ProcessReleaseSafety.release_resume_event process_source_event source_socket_request source_socket_bytes].
    rewrite FD,Int.eq_true;reflexivity.
Qed.

Theorem queue_actual_parent_source cell e pair parameters before suffix final request
    (shape:NamespaceUsefulParentShape cell e pair parameters before suffix final request):
  Forall queue_namespace_profile suffix /\queue_namespace_payload suffix=[Byte.repr 165].
Proof.
  destruct(queue_prefix_profile _(useful_prefix_profile _ _ _ _ _ _ _ _ shape))as[PREFIX BEFORE].
  destruct(queue_callback_profile _ _ _ _ _ _(useful_callback_shape _ _ _ _ _ _ _ _ shape))as[CALLBACK MIDDLE].
  rewrite(useful_parent_event_order _ _ _ _ _ _ _ _ shape),(useful_release_shape _ _ _ _ _ _ _ _ shape).
  destruct(queue_release_profile request(useful_request_descriptor _ _ _ _ _ _ _ _ shape)
    (useful_request_writing _ _ _ _ _ _ _ _ shape))as[RELEASE LAST].
  split;[repeat(apply Forall_app;split);assumption|].
  rewrite !queue_namespace_payload_append,BEFORE,MIDDLE,LAST;reflexivity.
Qed.

Theorem actual_parent_recording_grant_queue groups program namespace_id child_table ordinal world events ticks after_namespace after_world
    cell e pair parameters before suffix final request
    (shape:NamespaceUsefulParentShape cell e pair parameters before suffix final request):
  suffix=map namespace_process events ->
  ParentRecording groups program namespace_id child_table ordinal fork_fixture_world world events ticks after_namespace after_world ->
  forall buffers,physical_queue_execution 60 buffers ticks(channel_enqueue buffers 1 parent_endpoint[Byte.repr 165]).
Proof.
  intros EVENTS RECORDING buffers.
  destruct(queue_actual_parent_source _ _ _ _ _ _ _ _ shape)as[PROFILE PAYLOAD].
  rewrite EVENTS in PROFILE,PAYLOAD.
  rewrite queue_namespace_map_payload in PAYLOAD.
  destruct(queue_parent_recording_execution _ _ _ _ _ _ _ _ _ _ _ RECORDING
    (queue_namespace_map_profiles _ PROFILE)queue_fork_parent_slots queue_fork_parent_peer buffers)as[QUEUES PEER].
  rewrite PAYLOAD in QUEUES;exact QUEUES.
Qed.
