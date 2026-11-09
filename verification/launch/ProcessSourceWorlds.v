(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Keep the actual parent primitives in one physical process world. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership
  ProcessPhysicalTrace ProcessSourceRecording ProcessSourceTables ProcessCgroupRecording.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.

Lemma source_interference_refl parent child world:ProcessInterference parent child world world.
Proof. constructor;try reflexivity;auto. Qed.

Lemma source_interference_phase parent child before after:
  OwnsUnreaped before parent child ->ProcessInterference parent child before after ->
  owned_phase(process_tasks before child)=task_exited ->
  owned_phase(process_tasks after child)=task_exited.
Proof.
  intros OWNER STEP EXITED;destruct STEP as[before after PID PARENT GROUP PHASE FILE REAP SOLE|
    before after pid replacement FREE NUMBER NEW PID TASK FILE REAP SOLE];[auto|].
  assert(OTHER:child<>replacement).
  { intro SAME;subst replacement;rewrite <-NUMBER in FREE;destruct OWNER as[OWNED REST];congruence. }
  rewrite TASK by exact OTHER;exact EXITED.
Qed.

Lemma source_interference_waiter parent child before after:
  ProcessInterference parent child before after ->
  process_explicit_reap after parent=process_explicit_reap before parent /\
  process_sole_waiter after parent=process_sole_waiter before parent.
Proof. intro STEP;destruct STEP;auto. Qed.

Lemma source_interference_compose parent child before middle after:
  OwnsUnreaped before parent child ->ProcessInterference parent child before middle ->
  ProcessInterference parent child middle after ->ProcessInterference parent child before after.
Proof.
  intros OWNER FIRST SECOND.
  pose proof(unreaped_owner_survives_interference _ _ _ _ OWNER FIRST)as MIDDLE.
  pose proof(unreaped_owner_survives_interference _ _ _ _ MIDDLE SECOND)as AFTER.
  apply process_interference_frame.
  - destruct OWNER as[PID REST],AFTER as[NEW REST'];congruence.
  - destruct OWNER as[PID[PARENT REST]],AFTER as[NEW[NEWPARENT REST']];congruence.
  - rewrite(interference_owned_scope _ _ _ _ MIDDLE SECOND).
    exact(interference_owned_scope _ _ _ _ OWNER FIRST).
  - intro EXITED;eapply source_interference_phase;[exact MIDDLE|exact SECOND|].
    exact(source_interference_phase parent child before middle OWNER FIRST EXITED).
  - rewrite(interference_files _ _ _ _ SECOND);exact(interference_files _ _ _ _ FIRST).
  - destruct(source_interference_waiter _ _ _ _ FIRST)as[FIRST_REAP FIRST_SOLE].
    destruct(source_interference_waiter _ _ _ _ SECOND)as[SECOND_REAP SECOND_SOLE];congruence.
  - destruct(source_interference_waiter _ _ _ _ FIRST)as[FIRST_REAP FIRST_SOLE].
    destruct(source_interference_waiter _ _ _ _ SECOND)as[SECOND_REAP SECOND_SOLE];congruence.
Qed.

(* Parent death means an exited caller. A previously issued syscall may commit
   before that exit; it does not authorize another source operation afterward. *)
Definition SourceParentView world parent(context:LeanCage_Entry_CallerPhysical_Context):Prop:=
  owned_phase(process_tasks world parent)=task_exited <->
    LeanCage_Entry_CallerPhysical_Context_parentAlive context=ProcessImport.Bool_false.

Record SourceOtherContract
    (other:ProcessWorld->LeanCage_Entry_CallerPhysical_Tick->ProcessWorld->Prop)
    (groups:nat->option nat)(parent child:TaskIdentity):Prop:={
  source_other_interference:forall before tick after,
    OwnsUnreaped before parent child ->other before tick after ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick ->
    LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_after tick)=
      ProcessImport.Bool_true ->
    ProcessInterference parent child before after
}.

(* This interpreter starts at the same local fork with its consumed source
   cursor. The tracked parent's actual primitives share one ProcessWorld.
   Other ticks use a genuine operation relation; the Linux frame law above
   requires their actual object authority and a still-live owning parent. *)
Inductive SourceProcessStep operation groups child runs tracked
    (other:ProcessWorld->LeanCage_Entry_CallerPhysical_Tick->ProcessWorld->Prop):
    (nat->nat)->(nat->NamespaceWorld)->ProcessWorld->LeanCage_Entry_CallerPhysical_Tick->
    (nat->nat)->(nat->NamespaceWorld)->ProcessWorld->Prop:=
| source_process_parent:forall cursor worlds tick run original snapshot,
    nth_error runs tracked=Some run ->
    nth_error(source_events run)(cursor tracked)=Some(namespace_process original) ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference tracked(cursor tracked) ->
    SourcePrimitive operation groups child(source_actor run)(namespace_process original)tick snapshot ->
    source_namespace_before snapshot=worlds tracked ->
    SourceParentView(source_process_before snapshot)(physical_identity_task(source_actor run))
      (LeanCage_Entry_CallerPhysical_Tick_before tick) ->
    SourceParentView(source_process_after snapshot)(physical_identity_task(source_actor run))
      (LeanCage_Entry_CallerPhysical_Tick_after tick) ->
    SourceProcessStep operation groups child runs tracked other cursor worlds(source_process_before snapshot)tick
      (source_cursor_next cursor tracked)(source_world_next worlds tracked(source_namespace_after snapshot))
      (source_process_after snapshot)
| source_process_other:forall cursor worlds before tick middle middle_worlds after,
    SourceTableStep(SourcePrimitive operation groups child)runs cursor worlds tick middle middle_worlds ->
    (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference tracked ordinal) ->
    other before tick after ->
    SourceProcessStep operation groups child runs tracked other cursor worlds before tick middle middle_worlds after.

Inductive SourceProcessSchedule operation groups child runs tracked other:
    (nat->nat)->(nat->NamespaceWorld)->ProcessWorld->list LeanCage_Entry_CallerPhysical_Tick->
    (nat->nat)->(nat->NamespaceWorld)->ProcessWorld->Prop:=
| source_process_done:forall cursor worlds world,
    SourceProcessSchedule operation groups child runs tracked other cursor worlds world[]cursor worlds world
| source_process_cons:forall cursor worlds before tick middle middle_worlds observed ticks final final_worlds after,
    SourceProcessStep operation groups child runs tracked other cursor worlds before tick middle middle_worlds observed ->
    SourceProcessSchedule operation groups child runs tracked other middle middle_worlds observed ticks final final_worlds after ->
    SourceProcessSchedule operation groups child runs tracked other cursor worlds before(tick::ticks)final final_worlds after.

Theorem source_process_schedule_tables operation groups child runs tracked other cursor worlds before ticks
    final final_worlds after:
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds.
Proof.
  intro RUN;induction RUN;[constructor|].
  eapply source_table_cons;[|exact IHRUN].
  destruct H.
  - eapply source_table_next;eassumption.
  - exact H.
Qed.

Theorem source_process_schedule_split operation groups child runs tracked other cursor worlds before prefix suffix
    final final_worlds after:
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before(prefix++suffix)
    final final_worlds after ->
  exists middle middle_worlds boundary,
    SourceProcessSchedule operation groups child runs tracked other cursor worlds before prefix
      middle middle_worlds boundary /\
    SourceProcessSchedule operation groups child runs tracked other middle middle_worlds boundary suffix
      final final_worlds after.
Proof.
  revert cursor worlds before;induction prefix as[|tick ticks IH];intros cursor worlds before RUN;cbn in RUN.
  - exists cursor,worlds,before;split;[constructor|exact RUN].
  - inversion RUN as[|a b c d middle middle_worlds observed rest e f g STEP TAIL];subst.
    destruct(IH _ _ _ TAIL)as[next[next_worlds[boundary[FIRST SECOND]]]].
    exists next,next_worlds,boundary;split;[econstructor;eassumption|exact SECOND].
Qed.

Theorem source_process_step_selected operation groups child runs tracked other cursor worlds before tick
    middle middle_worlds after ordinal:
  SourceProcessStep operation groups child runs tracked other cursor worlds before tick middle middle_worlds after ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference tracked ordinal ->
  exists run original snapshot,nth_error runs tracked=Some run /\
    nth_error(source_events run)ordinal=Some(namespace_process original) /\
    SourcePrimitive operation groups child(source_actor run)(namespace_process original)tick snapshot /\
    source_process_before snapshot=before /\source_process_after snapshot=after /\
    SourceParentView before(physical_identity_task(source_actor run))(LeanCage_Entry_CallerPhysical_Tick_before tick).
Proof.
  intros STEP SOURCE;destruct STEP as[cursor worlds tick run original snapshot PROGRAM EVENT REFERENCE PRIMITIVE
    BEFORE PARENT_BEFORE PARENT_AFTER|cursor worlds before tick middle middle_worlds after TABLE OUTSIDE OTHER].
  - assert(SAME:source_reference tracked(cursor tracked)=source_reference tracked ordinal)by congruence.
    destruct(source_reference_injective _ _ _ _ SAME)as[_ ORDINAL];subst ordinal.
    exists run,original,snapshot;split;[exact PROGRAM|]. split;[exact EVENT|].
    split;[exact PRIMITIVE|]. split;[reflexivity|]. split;[reflexivity|exact PARENT_BEFORE].
  - exfalso;exact(OUTSIDE ordinal SOURCE).
Qed.

Theorem source_process_parent_live operation groups child actor event tick snapshot:
  SourcePrimitive operation groups child actor event tick snapshot ->
  SourceParentView(source_process_before snapshot)(physical_identity_task actor)
    (LeanCage_Entry_CallerPhysical_Tick_before tick) ->
  LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_before tick)=
    ProcessImport.Bool_true.
Proof.
  intros PRIMITIVE VIEW.
  destruct(LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_before tick))eqn:LIVE;
    [|reflexivity].
  exfalso;apply(source_primitive_caller_live _ _ _ _ _ _ _ PRIMITIVE).
  apply VIEW;exact LIVE.
Qed.

Definition source_program_process_events runs tracked ticks:=
  flat_map(fun event=>match event with namespace_process original=>[original]|_=>[]end)
    (source_program_events runs tracked ticks).

Lemma source_program_event_outside runs tracked tick:
  (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference tracked ordinal) ->
  source_program_event runs tracked tick=[].
Proof.
  intro OUTSIDE;unfold source_program_event.
  destruct(LeanCage_Entry_CallerPhysical_Tick_source tick)as[|[program ordinal]]eqn:SOURCE;[reflexivity|].
  destruct(Nat.eqb tracked(nat_of_Nat program))eqn:SAME;[|reflexivity].
  apply Nat.eqb_eq in SAME;subst tracked.
  exfalso;apply(OUTSIDE(nat_of_Nat ordinal));try rewrite SOURCE.
  unfold source_reference;rewrite !Nat2natid;reflexivity.
Qed.

Lemma source_world_pre_interference operation parent child before middle event events after:
  OwnsUnreaped before parent child ->ProcessInterference parent child before middle ->
  process_world_steps operation parent child middle(event::events)after ->
  process_world_steps operation parent child before(event::events)after.
Proof.
  intros OWNER FIRST RUN;inversion RUN;subst.
  econstructor;[eapply source_interference_compose;[exact OWNER|exact FIRST|eassumption]|eassumption|eassumption].
Qed.

Record SourceOtherAuthority groups tracked(ticks:list LeanCage_Entry_CallerPhysical_Tick):Prop:={
  source_other_quiet:forall tick,In tick ticks ->
    (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference tracked ordinal) ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick;
  source_other_live:forall tick,In tick ticks ->
    (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference tracked ordinal) ->
    LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_after tick)=
      ProcessImport.Bool_true
}.

Theorem source_other_authority_from_recorded_live groups tracked start limit prefix ticks suffix:
  LeanCage_Entry_CallerPhysical_ParentLiveBefore(Nat_of_nat start)
    (tick_values(prefix++ticks++suffix))(Nat_of_nat limit) ->
  (start+length prefix+length ticks<=limit)%nat ->
  (forall tick,In tick ticks ->
    (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference tracked ordinal) ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick) ->
  SourceOtherAuthority groups tracked ticks.
Proof.
  intros LIVE BOUND QUIET;constructor;[exact QUIET|].
  intros tick MEMBER OUTSIDE.
  apply In_nth_error in MEMBER;destruct MEMBER as[offset SELECTED].
  assert(OFFSET:(offset<length ticks)%nat)by(eapply nth_error_Some;rewrite SELECTED;discriminate).
  assert(POSITION:nth_error(prefix++ticks++suffix)(length prefix+offset)=Some tick).
  { rewrite nth_error_app2 by lia.
    replace(length prefix+offset-length prefix)%nat with offset by lia.
    rewrite nth_error_app1 by exact OFFSET;exact SELECTED. }
  assert(LESS:(ProcessImport.Nat_add(Nat_of_nat start)(Nat_of_nat(length prefix+offset))<Nat_of_nat limit)%Nat).
  { apply nat_le_Nat_le;rewrite physical_succ_exact,physical_add_exact,!nat2Natid;lia. }
  pose proof(LIVE(Nat_of_nat(length prefix+offset))tick LESS(actual_tick_position _ _ _ POSITION))as CHECK.
  destruct CHECK;reflexivity.
Qed.

Theorem source_process_schedule_projects operation(linux:LinuxProcessContract operation)
    groups child runs tracked other parent cursor worlds before ticks final final_worlds after:
  SourceOtherContract other groups parent(physical_identity_task child) ->
  (forall run,nth_error runs tracked=Some run ->physical_identity_task(source_actor run)=parent) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  OwnsUnreaped before parent(physical_identity_task child) ->SourceOtherAuthority groups tracked ticks ->
  Forall(fun event=>process_nonreaping event=true)(source_program_process_events runs tracked ticks) ->
  exists boundary,
    process_world_steps operation parent(physical_identity_task child)before
      (source_program_process_events runs tracked ticks)boundary /\
    ProcessInterference parent(physical_identity_task child)boundary after /\
    OwnsUnreaped after parent(physical_identity_task child).
Proof.
  intros CONTRACT ACTOR RUN;induction RUN;intros OWNER AUTHORITY EVENTS.
  - exists world;split;[constructor|]. split;[apply source_interference_refl|exact OWNER].
  - assert(TAIL_AUTHORITY:SourceOtherAuthority groups tracked ticks).
    { constructor;intros selected MEMBER OUTSIDE.
      - eapply source_other_quiet;[exact AUTHORITY|right;exact MEMBER|exact OUTSIDE].
      - eapply source_other_live;[exact AUTHORITY|right;exact MEMBER|exact OUTSIDE]. }
    destruct H as[cursor worlds tick run original snapshot PROGRAM EVENT SOURCE PRIMITIVE BEFORE PARENT_BEFORE PARENT_AFTER|
      cursor worlds before tick middle middle_worlds observed STEP OUTSIDE OTHER].
    + unfold source_program_process_events,source_program_events in EVENTS|-*;cbn in EVENTS|-*.
      unfold source_program_event in EVENTS|-*;rewrite SOURCE in EVENTS|-*.
      cbn[source_reference]in EVENTS|-*;rewrite !nat2Natid,Nat.eqb_refl,PROGRAM,EVENT in EVENTS|-*.
      cbn in EVENTS|-*;inversion EVENTS as[|head tail NONREAP REMAINING];subst head tail.
      pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE original(Logic.eq_refl _))as KERNEL.
      rewrite(ACTOR _ PROGRAM)in KERNEL.
      assert(NEXT_OWNER:OwnsUnreaped(source_process_after snapshot)parent(physical_identity_task child)).
      { eapply(linux_nonreaping_owner _ linux);[exact OWNER|exact NONREAP|exact KERNEL]. }
      destruct(IHRUN NEXT_OWNER TAIL_AUTHORITY REMAINING)as[boundary[REST[INTERFERENCE FINAL_OWNER]]].
      exists boundary;split.
      * econstructor;[apply source_interference_refl|exact KERNEL|exact REST].
      * split;assumption.
    + pose proof(source_program_event_outside runs tracked tick OUTSIDE)as EMPTY.
      unfold source_program_process_events,source_program_events in EVENTS|-*;cbn in EVENTS|-*.
      rewrite EMPTY in EVENTS|-*;cbn in EVENTS|-*.
      pose proof(source_other_quiet _ _ _ AUTHORITY tick ltac:(left;reflexivity)OUTSIDE)as QUIET.
      pose proof(source_other_live _ _ _ AUTHORITY tick ltac:(left;reflexivity)OUTSIDE)as LIVE.
      pose proof(source_other_interference _ _ _ _ CONTRACT _ _ _ OWNER OTHER QUIET LIVE)as INTERFERENCE.
      assert(NEXT_OWNER:OwnsUnreaped observed parent(physical_identity_task child))
        by(eapply unreaped_owner_survives_interference;[exact OWNER|exact INTERFERENCE]).
      destruct(IHRUN NEXT_OWNER TAIL_AUTHORITY EVENTS)as[boundary[REST[TRAILING FINAL_OWNER]]].
      destruct(flat_map
        (fun event=>match event with namespace_process original=>[original]|_=>[]end)
        (flat_map(source_program_event runs tracked)ticks))as[|event events]eqn:OBSERVED_EVENTS.
      * change(source_program_process_events runs tracked ticks=[])in OBSERVED_EVENTS.
        rewrite OBSERVED_EVENTS in REST;inversion REST;subst boundary;exists before;split;[constructor|].
        split;[eapply source_interference_compose;eassumption|exact FINAL_OWNER].
      * change(source_program_process_events runs tracked ticks=event::events)in OBSERVED_EVENTS.
        rewrite OBSERVED_EVENTS in REST.
        exists boundary;split;[eapply source_world_pre_interference;eassumption|].
        split;assumption.
Qed.

Theorem source_process_schedule_scope operation(linux:LinuxProcessContract operation)
    groups child runs tracked other parent cursor worlds before ticks final final_worlds after group:
  SourceOtherContract other groups parent(physical_identity_task child) ->
  (forall run,nth_error runs tracked=Some run ->physical_identity_task(source_actor run)=parent) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  OwnsUnreaped before parent(physical_identity_task child) ->
  owned_cgroup(process_tasks before(physical_identity_task child))=Some group ->
  SourceOtherAuthority groups tracked ticks ->
  Forall(fun event=>process_quiet_event event=true)(source_program_process_events runs tracked ticks) ->
  OwnsUnreaped after parent(physical_identity_task child) /\
    owned_cgroup(process_tasks after(physical_identity_task child))=Some group.
Proof.
  intros CONTRACT ACTOR RUN OWNER GROUP AUTHORITY QUIET.
  assert(NONREAP:Forall(fun event=>process_nonreaping event=true)
    (source_program_process_events runs tracked ticks)).
  { apply Forall_forall;intros event MEMBER;apply Forall_forall with(x:=event)in QUIET;[|exact MEMBER].
    unfold process_quiet_event in QUIET;apply Bool.andb_true_iff in QUIET;exact(proj1 QUIET). }
  destruct(source_process_schedule_projects operation linux groups child runs tracked other parent cursor worlds before
    ticks final final_worlds after CONTRACT ACTOR RUN OWNER AUTHORITY NONREAP)
    as[boundary[STEPS[INTERFERENCE FINAL_OWNER]]].
  destruct(process_trace_retains_scope _ linux _ _ _ _ _ OWNER QUIET STEPS)as[BOUND_OWNER FRAME].
  split;[exact FINAL_OWNER|].
  rewrite(interference_owned_scope _ _ _ _ BOUND_OWNER INTERFERENCE),FRAME;exact GROUP.
Qed.


(* Select ownership from the actual prefix; a later syscall does not receive
   a new reap token or an independently prepared process snapshot. *)
Theorem source_process_selected_before_owner operation(linux:LinuxProcessContract operation)
    groups child runs tracked other parent cursor worlds before prefix tick suffix final final_worlds after ordinal:
  SourceOtherContract other groups parent(physical_identity_task child) ->
  (forall run,nth_error runs tracked=Some run ->physical_identity_task(source_actor run)=parent) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before(prefix++tick::suffix)
    final final_worlds after ->
  SourceOtherAuthority groups tracked(prefix++tick::suffix) ->
  OwnsUnreaped before parent(physical_identity_task child) ->
  Forall(fun event=>process_nonreaping event=true)
    (source_program_process_events runs tracked(prefix++tick::suffix)) ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference tracked ordinal ->
  exists run original snapshot,nth_error runs tracked=Some run /\
    nth_error(source_events run)ordinal=Some(namespace_process original) /\
    SourcePrimitive operation groups child(source_actor run)(namespace_process original)tick snapshot /\
    OwnsUnreaped(source_process_before snapshot)parent(physical_identity_task child).
Proof.
  intros CONTRACT ACTOR RUN AUTHORITY OWNER NONREAP REFERENCE.
  assert(PREFIX_AUTH:SourceOtherAuthority groups tracked prefix).
  { constructor;intros selected MEMBER OUTSIDE.
    - eapply source_other_quiet;[exact AUTHORITY|apply in_or_app;left;exact MEMBER|exact OUTSIDE].
    - eapply source_other_live;[exact AUTHORITY|apply in_or_app;left;exact MEMBER|exact OUTSIDE]. }
  assert(PREFIX_NONREAP:Forall(fun event=>process_nonreaping event=true)
    (source_program_process_events runs tracked prefix)).
  { unfold source_program_process_events,source_program_events in NONREAP|-*.
    rewrite flat_map_app,flat_map_app in NONREAP;apply Forall_app in NONREAP;exact(proj1 NONREAP). }
  destruct(source_process_schedule_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)
    as[middle[middle_worlds[boundary[PREFIX SUFFIX]]]].
  destruct(source_process_schedule_projects operation linux groups child runs tracked other parent cursor worlds before
    prefix middle middle_worlds boundary CONTRACT ACTOR PREFIX OWNER PREFIX_AUTH PREFIX_NONREAP)
    as[last[STEPS[INTERFERENCE BOUND_OWNER]]].
  inversion SUFFIX as[|a b c d next next_worlds observed rest e f g STEP TAIL];subst.
  destruct(source_process_step_selected _ _ _ _ _ _ _ _ _ _ _ _ _ _ STEP REFERENCE)
    as[run[original[snapshot[PROGRAM[EVENT[PRIMITIVE[BEFORE[AFTER VIEW]]]]]]]].
  exists run,original,snapshot;split;[exact PROGRAM|]. split;[exact EVENT|].
  split;[exact PRIMITIVE|]. rewrite BEFORE;exact BOUND_OWNER.
Qed.
