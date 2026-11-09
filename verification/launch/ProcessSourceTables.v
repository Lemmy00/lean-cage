(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Preserve private C caller tables between exact source occurrences. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessSourceRecording ProcessScope.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.

Definition source_world_next(before:nat->NamespaceWorld)program after:=
  fun query=>if Nat.eqb query program then after else before query.

(* The runtime owns distinct, non-CLONE_FILES C caller tables. A source tick
   changes its own table through the actual Linux primitive; a tick outside
   these callers frames their private tables. This is an operation-level FD
   ownership contract, not a cgroup or authorized-release property. *)
Inductive SourceTableStep
    (primitive:LeanCage_Entry_ProcessIdentity->namespace_event->
      LeanCage_Entry_CallerPhysical_Tick->SourceSnapshot->Prop)
    (runs:list CallerSourceRun):
    (nat->nat)->(nat->NamespaceWorld)->LeanCage_Entry_CallerPhysical_Tick->
    (nat->nat)->(nat->NamespaceWorld)->Prop:=
| source_table_external:forall cursor worlds tick,
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference ->
    SourceTableStep primitive runs cursor worlds tick cursor worlds
| source_table_next:forall cursor worlds tick run program event snapshot,
    nth_error runs program=Some run ->
    nth_error(source_events run)(cursor program)=Some event ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program(cursor program) ->
    primitive(source_actor run)event tick snapshot ->
    source_namespace_before snapshot=worlds program ->
    SourceTableStep primitive runs cursor worlds tick(source_cursor_next cursor program)
      (source_world_next worlds program(source_namespace_after snapshot)).

Inductive SourceTableSchedule primitive runs:
    (nat->nat)->(nat->NamespaceWorld)->list LeanCage_Entry_CallerPhysical_Tick->
    (nat->nat)->(nat->NamespaceWorld)->Prop:=
| source_table_done:forall cursor worlds,SourceTableSchedule primitive runs cursor worlds[]cursor worlds
| source_table_cons:forall cursor worlds tick middle middle_worlds ticks final final_worlds,
    SourceTableStep primitive runs cursor worlds tick middle middle_worlds ->
    SourceTableSchedule primitive runs middle middle_worlds ticks final final_worlds ->
    SourceTableSchedule primitive runs cursor worlds(tick::ticks)final final_worlds.

Theorem source_table_schedule_erases primitive runs cursor worlds ticks final final_worlds:
  SourceTableSchedule primitive runs cursor worlds ticks final final_worlds ->
  SourceEventSchedule primitive runs cursor ticks final.
Proof.
  intro RUN;induction RUN.
  - constructor.
  - destruct H.
    + eapply source_event_external;eassumption.
    + eapply source_event_next;eassumption.
Qed.

Theorem source_table_schedule_split primitive runs cursor worlds prefix suffix final final_worlds:
  SourceTableSchedule primitive runs cursor worlds(prefix++suffix)final final_worlds ->
  exists middle middle_worlds,
    SourceTableSchedule primitive runs cursor worlds prefix middle middle_worlds /\
    SourceTableSchedule primitive runs middle middle_worlds suffix final final_worlds.
Proof.
  revert cursor worlds;induction prefix as[|tick ticks IH];intros cursor worlds RUN;cbn in RUN.
  - exists cursor,worlds;split;[constructor|exact RUN].
  - inversion RUN as[|a b c middle middle_worlds rest d e STEP TAIL];subst.
    destruct(IH _ _ TAIL)as[boundary[boundary_worlds[FIRST SECOND]]].
    exists boundary,boundary_worlds;split;[econstructor;eassumption|exact SECOND].
Qed.

Theorem source_table_step_selected primitive runs cursor worlds tick middle middle_worlds program ordinal:
  SourceTableStep primitive runs cursor worlds tick middle middle_worlds ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  exists run event snapshot,nth_error runs program=Some run /\
    nth_error(source_events run)ordinal=Some event /\primitive(source_actor run)event tick snapshot /\
    source_namespace_before snapshot=worlds program /\
    middle_worlds=source_world_next worlds program(source_namespace_after snapshot).
Proof.
  intros STEP SOURCE;destruct STEP as[cursor worlds tick OUTSIDE|
    cursor worlds tick run selected event snapshot PROGRAM EVENT REFERENCE PRIMITIVE BEFORE].
  - rewrite SOURCE in OUTSIDE;discriminate.
  - assert(SAME:source_reference selected(cursor selected)=source_reference program ordinal)by congruence.
    destruct(source_reference_injective _ _ _ _ SAME)as[SELECTED ORDINAL];subst selected ordinal.
    exists run,event,snapshot;repeat split;assumption||reflexivity.
Qed.

Definition SourceNamespaceLaw
    (primitive:LeanCage_Entry_ProcessIdentity->namespace_event->
      LeanCage_Entry_CallerPhysical_Tick->SourceSnapshot->Prop):Prop:=
  forall actor event tick snapshot,primitive actor event tick snapshot ->
    namespace_kernel_event(source_namespace_before snapshot)event(source_namespace_after snapshot).

Theorem source_primitive_namespace_law operation groups child:
  SourceNamespaceLaw(SourcePrimitive operation groups child).
Proof. intros actor event tick snapshot PRIMITIVE;eapply source_primitive_namespace;exact PRIMITIVE. Qed.

Definition source_program_event runs query(tick:LeanCage_Entry_CallerPhysical_Tick):list namespace_event:=
  match LeanCage_Entry_CallerPhysical_Tick_source tick with
  |ProcessImport.Option_none_inst1 _=>[]
  |ProcessImport.Option_some_inst1 _ reference=>match reference with
    |LeanCage_Entry_CallerPhysical_SourceReference_mk selected ordinal=>
      if Nat.eqb query(nat_of_Nat selected)then
        match nth_error runs(nat_of_Nat selected)with
        |None=>[]|Some run=>match nth_error(source_events run)(nat_of_Nat ordinal)with
          |None=>[]|Some event=>[event]end end
      else[]end end.
Definition source_program_events runs query ticks:=flat_map(source_program_event runs query)ticks.

Lemma source_skip_selected(A:Type)(values:list A)index value:
  nth_error values index=Some value ->skipn index values=value::skipn(S index)values.
Proof.
  revert index;induction values as[|first rest IH];intros[|index]SELECTED;try discriminate;cbn in *.
  - inversion SELECTED;reflexivity.
  - apply IH;exact SELECTED.
Qed.

Theorem source_event_schedule_program_events primitive runs cursor ticks final program run:
  SourceEventSchedule primitive runs cursor ticks final ->nth_error runs program=Some run ->
  source_program_events runs program ticks=
    firstn(final program-cursor program)(skipn(cursor program)(source_events run)).
Proof.
  intro RUN;induction RUN;intro PROGRAM.
  - cbn[source_program_events];replace(before program-before program)%nat with 0%nat by lia;reflexivity.
  - unfold source_program_events in *;cbn;unfold source_program_event;rewrite H;apply IHRUN;exact PROGRAM.
  - unfold source_program_events in *;cbn;unfold source_program_event;rewrite H1.
    cbn[source_reference];rewrite !nat2Natid.
    destruct(Nat.eq_dec program program0)as[SAME|OTHER].
    + subst program0;rewrite Nat.eqb_refl,H,H0;cbn.
      assert(SAME_RUN:run0=run)by congruence;subst run0.
      fold(source_program_event runs program).
      rewrite(IHRUN PROGRAM).
      unfold source_cursor_next;rewrite Nat.eqb_refl.
      pose proof(source_schedule_monotone _ _ _(source_event_schedule_erases _ _ _ _ _ RUN)program)as HIGH.
      unfold source_cursor_next in HIGH;rewrite Nat.eqb_refl in HIGH.
      replace(after program-before program)%nat with(S(after program-S(before program)))by lia.
      rewrite(source_skip_selected _ _ _ _ H0);reflexivity.
    + assert(DIFFERENT:Nat.eqb program program0=false)by(apply Nat.eqb_neq;exact OTHER).
      rewrite DIFFERENT;fold(source_program_event runs program);rewrite(IHRUN PROGRAM).
      unfold source_cursor_next;rewrite DIFFERENT;reflexivity.
Qed.

Theorem source_table_schedule_program_events primitive runs cursor worlds ticks final final_worlds program run:
  SourceTableSchedule primitive runs cursor worlds ticks final final_worlds ->nth_error runs program=Some run ->
  source_program_events runs program ticks=
    firstn(final program-cursor program)(skipn(cursor program)(source_events run)).
Proof.
  intros RUN PROGRAM;eapply source_event_schedule_program_events;
    [eapply source_table_schedule_erases;exact RUN|exact PROGRAM].
Qed.

Theorem source_table_schedule_projects primitive runs cursor worlds ticks final final_worlds query:
  SourceNamespaceLaw primitive ->
  SourceTableSchedule primitive runs cursor worlds ticks final final_worlds ->
  namespace_kernel_steps(worlds query)(source_program_events runs query ticks)(final_worlds query).
Proof.
  intros LAW RUN;induction RUN;[constructor|].
  unfold source_program_events in *;cbn;destruct H as[cursor worlds tick OUTSIDE|
    cursor worlds tick run selected event snapshot PROGRAM EVENT REFERENCE PRIMITIVE BEFORE].
  - unfold source_program_event;rewrite OUTSIDE;exact IHRUN.
  - unfold source_program_event;rewrite REFERENCE.
    cbn[source_reference];rewrite !nat2Natid.
    destruct(Nat.eqb query selected)eqn:SAME.
    + apply Nat.eqb_eq in SAME;subst query;rewrite PROGRAM,EVENT;cbn.
      eapply namespace_kernel_cons;[rewrite <-BEFORE;eapply LAW;exact PRIMITIVE|].
      unfold source_world_next in IHRUN;rewrite Nat.eqb_refl in IHRUN;exact IHRUN.
    + unfold source_world_next in IHRUN;rewrite SAME in IHRUN;exact IHRUN.
Qed.

Theorem source_table_before_selected primitive runs cursor worlds ticks final final_worlds
    later_offset later_tick program later_ordinal earlier_ordinal run event:
  SourceTableSchedule primitive runs cursor worlds ticks final final_worlds ->
  nth_error ticks later_offset=Some later_tick ->
  LeanCage_Entry_CallerPhysical_Tick_source later_tick=source_reference program later_ordinal ->
  (cursor program<=earlier_ordinal<later_ordinal)%nat ->
  nth_error runs program=Some run ->nth_error(source_events run)earlier_ordinal=Some event ->
  exists offset tick snapshot,(offset<later_offset)%nat /\nth_error ticks offset=Some tick /\
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program earlier_ordinal /\
    primitive(source_actor run)event tick snapshot.
Proof.
  intros RUN LATER SOURCE ORDER PROGRAM EVENT.
  pose proof(source_table_schedule_erases _ _ _ _ _ _ _ RUN)as EVENTS.
  pose proof(source_event_schedule_erases _ _ _ _ _ EVENTS)as SCHEDULE.
  destruct(source_schedule_selected _ _ _ _ _ _ _ SCHEDULE LATER SOURCE)as[LOW HIGH].
  assert(BOUNDS:(cursor program<=earlier_ordinal<final program)%nat)by lia.
  destruct(source_event_schedule_covers primitive runs cursor ticks final program earlier_ordinal run event
    EVENTS BOUNDS PROGRAM EVENT)
    as[offset[tick[snapshot[SELECTED[REFERENCE PRIMITIVE]]]]].
  exists offset,tick,snapshot;split.
  - eapply source_schedule_order_inverse;[exact SCHEDULE|exact(proj2 ORDER)|exact SELECTED|
      exact LATER|exact REFERENCE|exact SOURCE].
  - repeat split;assumption.
Qed.

Theorem source_table_schedule_absence primitive runs cursor worlds ticks final final_worlds query object:
  SourceNamespaceLaw primitive ->
  SourceTableSchedule primitive runs cursor worlds ticks final final_worlds ->
  object_absent(namespace_table(worlds query))(ordinary_object object) ->
  object_absent(namespace_table(final_worlds query))(ordinary_object object).
Proof.
  intros LAW RUN ABSENT;eapply namespace_ordinary_absence_trace;
    [eapply source_table_schedule_projects;eassumption|exact ABSENT].
Qed.

Theorem source_table_selected_absence operation groups child runs cursor worlds ticks final final_worlds
    offset tick program ordinal run object:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  nth_error ticks offset=Some tick ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  nth_error runs program=Some run ->
  object_absent(namespace_table(worlds program))(ordinary_object object) ->
  object_absent(physical_tick_table tick
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run))))
    (ordinary_object object).
Proof.
  intro RUN;revert offset;induction RUN;intros[|offset]SELECTED SOURCE PROGRAM ABSENT;try discriminate.
  - inversion SELECTED;subst.
    destruct(source_table_step_selected _ _ _ _ _ _ _ _ _ H SOURCE)
      as[actual[event[snapshot[ACTUAL[EVENT[PRIMITIVE[BEFORE AFTER]]]]]]].
    assert(SAME:actual=run)by congruence;subst actual.
    intros fd binding PRESENT OBJECT.
    rewrite(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE fd),BEFORE in PRESENT.
    eapply ABSENT;eassumption.
  - apply(IHRUN _ SELECTED SOURCE PROGRAM).
    eapply source_table_schedule_absence;
      [apply source_primitive_namespace_law|econstructor;[exact H|constructor]|exact ABSENT].
Qed.

Theorem source_table_close_later_absence operation groups child runs cursor worlds prefix close_tick rest
    final final_worlds program close_ordinal run fd reply offset later_tick later_ordinal:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds
    (prefix++close_tick::rest)final final_worlds ->
  LeanCage_Entry_CallerPhysical_Tick_source close_tick=source_reference program close_ordinal ->
  nth_error runs program=Some run ->
  nth_error(source_events run)close_ordinal=
    Some(namespace_process(process_entry(entry_library(close_returned fd reply)))) ->
  close_value reply=Int.zero ->nth_error rest offset=Some later_tick ->
  LeanCage_Entry_CallerPhysical_Tick_source later_tick=source_reference program later_ordinal ->
  exists snapshot,
    SourcePrimitive operation groups child(source_actor run)
      (namespace_process(process_entry(entry_library(close_returned fd reply))))close_tick snapshot /\
    namespace_kernel_steps(worlds program)(source_program_events runs program prefix)
      (source_namespace_before snapshot) /\
    forall object,
      unique_object_alias(namespace_table(source_namespace_before snapshot))(ordinary_object object)fd ->
      object_absent(physical_tick_table later_tick
        (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run))))(ordinary_object object).
Proof.
  intros RUN SOURCE PROGRAM EVENT ZERO LATER LATER_SOURCE.
  destruct(source_table_schedule_split _ _ _ _ _ _ _ _ RUN)
    as[middle[middle_worlds[PREFIX SUFFIX]]].
  inversion SUFFIX as[|a b c after after_worlds ticks d e STEP TAIL];subst.
  destruct(source_table_step_selected _ _ _ _ _ _ _ _ _ STEP SOURCE)
    as[actual[observed[snapshot[ACTUAL[OBSERVED[PRIMITIVE[BEFORE AFTER]]]]]]].
  assert(ACTUAL_RUN:actual=run)by congruence;subst actual.
  assert(ACTUAL_EVENT:observed=namespace_process(process_entry(entry_library(close_returned fd reply))))by congruence.
  subst observed.
  exists snapshot;split;[exact PRIMITIVE|]. split.
  - rewrite BEFORE;eapply source_table_schedule_projects;
      [apply source_primitive_namespace_law|exact PREFIX].
  - intros object UNIQUE.
    destruct(recorded_source_close operation groups child(source_actor run)_ close_tick snapshot fd reply
      PRIMITIVE(Logic.eq_refl _))as[ACTION CLOSE].
    assert(ABSENT:object_absent(namespace_table(source_namespace_after snapshot))(ordinary_object object)).
    { eapply successful_unique_close_removes_object;[exact UNIQUE|exact CLOSE|exact ZERO]. }
    eapply source_table_selected_absence;
      [exact TAIL|exact LATER|exact LATER_SOURCE|exact PROGRAM|].
    rewrite AFTER;unfold source_world_next;rewrite Nat.eqb_refl;exact ABSENT.
Qed.
