(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Preserve the parent's owned process through the same useful child source. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From compcert Require Import AST Integers Values Memory Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffTraceEvents NativeHandoffTrace.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds ProcessLaunchWitness ProcessLaunchRecordingWitness
  ProcessParentRecordingWitness ProcessChildRecordingWitness ProcessChildTickWitness.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceWorldTrace NamespacePhysical
  NamespaceSocket NamespaceGuestFlags NamespaceGuestImage NamespaceChildWorldWitness NamespacePaths.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Lemma child_good_flag_socket_none event:
  Forall namespace_good_flag(handoff_event_flags event) ->
  namespace_socket_io(namespace_guest_event event)=None.
Proof.
  destruct event;cbn[handoff_event_flags];intro GOOD;
    try reflexivity;try solve[inversion GOOD;contradiction].
  destruct event;cbn[handoff_event_flags]in GOOD|-*;
    try reflexivity;try solve[inversion GOOD;contradiction].
  destruct ev;cbn[handoff_event_flags]in GOOD|-*;
    try reflexivity;try solve[inversion GOOD;contradiction].
Qed.

Lemma child_good_flags_sockets_none events:
  Forall namespace_good_flag(handoff_flags_projection events) ->
  Forall(fun event=>namespace_socket_io(namespace_guest_event event)=None)events.
Proof.
  induction events as[|event events IH];intro GOOD;[constructor|].
  unfold handoff_flags_projection in GOOD;cbn[flat_map]in GOOD;apply Forall_app in GOOD as[HEAD TAIL].
  constructor;[apply child_good_flag_socket_none;exact HEAD|apply IH;exact TAIL].
Qed.

Theorem actual_guest_success_sockets_none cell input before k events target path arguments environment:
  handoff_borrowed_input cell before input ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 60)]k before))
    events target ->In(entry_image path arguments environment)events ->
  Forall(fun event=>namespace_socket_io(namespace_guest_event event)=None)events.
Proof.
  intros INPUT SOURCE IMAGE.
  destruct(handoff_guest_image_flags _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT SOURCE IMAGE)
    as[prefix[b[after[caller[suffix[waits[EVENTS[FLAGS[PREFIX[PATH[ARGS[ENV TARGET]]]]]]]]]]]].
  assert(GOOD:Forall namespace_good_flag(handoff_flags_projection prefix)).
  { rewrite FLAGS;unfold handoff_expected_flags;repeat(apply Forall_cons;
      [cbn[namespace_good_flag];auto|]);constructor. }
  rewrite EVENTS;apply Forall_app;split;[apply child_good_flags_sockets_none;exact GOOD|].
  apply Forall_app;split.
  - apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst event;reflexivity.
  - constructor;[reflexivity|constructor].
Qed.

Theorem actual_same_fork_child_sockets_none cell command source memory pair parameters k
    branch_memory b after caller prefix world:
  namespace_useful_child_image_fields cell command source memory pair parameters k
    branch_memory b after caller prefix world ->
  Forall(fun event=>namespace_socket_io event=None)(child_useful_namespace_events b prefix).
Proof.
  intro FIELDS;unfold namespace_useful_child_image_fields in FIELDS;cbn zeta in FIELDS.
  destruct FIELDS as[BORROWED[SNAPSHOT[BYTES[CANONICAL[CHILD_SOURCE[GUEST REST]]]]]].
  unfold child_useful_namespace_events;apply Forall_app;split.
  - repeat(apply Forall_app;split);apply Forall_forall;intros event MEMBER;
      apply repeat_spec in MEMBER;subst event;reflexivity.
  - apply Forall_map;eapply actual_guest_success_sockets_none;[exact BORROWED|exact GUEST|].
    apply in_or_app;right;left;reflexivity.
Qed.

Lemma launch_child_source_interference before event after:
  launch_operation physical_child before event after ->
  namespace_socket_io(namespace_process event)=None ->
  ProcessInterference physical_parent physical_child before after.
Proof.
  intros OP QUIET;destruct OP;try apply source_interference_refl;try discriminate.
  all:apply process_interference_frame;try reflexivity;try solve[intro EXITED;exact EXITED].
Qed.

(* This is a finite useful-run primitive observation. The source profile above
   establishes its quiet field from the actual successful guest path. *)
Inductive UsefulChildOther groups runs:ProcessWorld->LeanCage_Entry_CallerPhysical_Tick->ProcessWorld->Prop:=
| useful_child_source:forall run program ordinal original tick snapshot,
    nth_error runs program=Some run ->source_actor run=launch_recording_child ->
    nth_error(source_events run)ordinal=Some(namespace_process original) ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    SourcePrimitive launch_operation groups launch_recording_child launch_recording_child
      (namespace_process original)tick snapshot ->
    namespace_socket_io(namespace_process original)=None ->
    UsefulChildOther groups runs(source_process_before snapshot)tick(source_process_after snapshot).

Theorem useful_child_other_contract groups runs:
  SourceOtherContract(UsefulChildOther groups runs)groups physical_parent physical_child.
Proof.
  constructor;intros before tick after OWNER OTHER OUTSIDE LIVE.
  destruct OTHER as[run program ordinal original tick snapshot PROGRAM ACTOR EVENT REFERENCE PRIMITIVE QUIET].
  eapply launch_child_source_interference;[|exact QUIET].
  pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE original(Logic.eq_refl _))as OP.
  rewrite launch_recording_child_task in OP;exact OP.
Qed.

Theorem child_recording_other_schedule groups program namespace_id parent ordinal namespace world events ticks
    after_namespace after_world:
  ChildRecording groups program namespace_id parent ordinal namespace world events ticks after_namespace after_world ->
  Forall(fun event=>namespace_socket_io(namespace_process event)=None)events ->
  forall runs run prefix suffix cursor worlds tracked other,
    nth_error runs program=Some run ->source_actor run=launch_recording_child ->
    source_events run=prefix++map namespace_process events++suffix ->length prefix=ordinal ->
    cursor program=ordinal ->worlds program=namespace ->program<>tracked ->
    (forall before tick after,UsefulChildOther groups runs before tick after ->other before tick after) ->
    exists final final_worlds,
      SourceProcessSchedule launch_operation groups launch_recording_child runs tracked other
        cursor worlds world ticks final final_worlds after_world /\
      final program=(ordinal+length events)%nat /\final_worlds program=after_namespace /\
      forall query,query<>program ->final query=cursor query /\final_worlds query=worlds query.
Proof.
  intro RUN;induction RUN;intros QUIET runs run prefix suffix cursor worlds tracked other PROGRAM ACTOR EVENTS LENGTH CURSOR WORLD DIFFERENT INCLUDE.
  - exists cursor,worlds;split;[constructor|]. split;[cbn;lia|]. split;[exact WORLD|intros;auto].
  - inversion QUIET as[|actual rest HEAD TAIL];subst actual rest.
    assert(EVENT:nth_error(source_events run)(cursor program)=Some(namespace_process event)).
    { rewrite CURSOR,<-LENGTH,EVENTS;apply recording_head_event. }
    assert(REST:source_events run=(prefix++[namespace_process event])++map namespace_process events++suffix).
    { rewrite EVENTS;cbn[map];repeat rewrite <-app_assoc;reflexivity. }
    destruct(IHRUN TAIL runs run(prefix++[namespace_process event])suffix(source_cursor_next cursor program)
      (source_world_next worlds program next)tracked other PROGRAM ACTOR REST)
      as[final[final_worlds[TAIL_RUN[FINAL[AFTER FRAME]]]]].
    + rewrite length_app;cbn;lia.
    + rewrite recording_cursor_here,CURSOR;reflexivity.
    + apply recording_world_here.
    + exact DIFFERENT.
    + exact INCLUDE.
    + exists final,final_worlds;split.
      * eapply source_process_cons;[eapply source_process_other with(middle:=source_cursor_next cursor program)
          (middle_worlds:=source_world_next worlds program next)|exact TAIL_RUN].
        -- eapply source_table_next with(run:=run)(event:=namespace_process event)(snapshot:=snapshot).
           ++ exact PROGRAM.
           ++ exact EVENT.
           ++ change(source_reference program ordinal=source_reference program(cursor program));rewrite CURSOR;reflexivity.
           ++ rewrite ACTOR;exact H.
           ++ cbn[source_namespace_before];symmetry;exact WORLD.
        -- intros selected SAME;change(source_reference program ordinal=source_reference tracked selected)in SAME.
           destruct(source_reference_injective _ _ _ _ SAME)as[EQUAL POSITION];contradiction.
        -- apply INCLUDE;eapply useful_child_source with(run:=run)(program:=program)(ordinal:=cursor program)
             (original:=event)(snapshot:=snapshot).
           ++ exact PROGRAM.
           ++ exact ACTOR.
           ++ exact EVENT.
           ++ change(source_reference program ordinal=source_reference program(cursor program));rewrite CURSOR;reflexivity.
           ++ exact H.
           ++ exact HEAD.
      * split;[cbn;lia|]. split;[exact AFTER|].
        intros query OTHER;destruct(FRAME _ OTHER)as[POSITION TABLE].
        rewrite recording_cursor_other in POSITION by exact OTHER.
        rewrite recording_world_other in TABLE by exact OTHER;auto.
Qed.
