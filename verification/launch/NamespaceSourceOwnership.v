(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: The same source cursor and actual Linux operations preserve the private endpoint slots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessSourceRecording ProcessSourceTables.
From EntryNamespace Require Import NamespaceObjects NamespaceEndpoint NamespaceKernel NamespaceWorldTrace
  NamespacePhysical NamespaceDescriptorFrame.
Import ListNotations.
Local Close Scope lean_scope.

Lemma source_ownership_firstn(A:Type)(P:A->Prop)count values:Forall P values ->Forall P(firstn count values).
Proof.
  revert values;induction count;intros values GOOD;[constructor|destruct values;cbn;[constructor|]].
  inversion GOOD;subst;constructor;[assumption|apply IHcount;assumption].
Qed.

Theorem source_table_selected_object_frame operation groups child runs cursor worlds ticks final final_worlds
    offset tick program ordinal run:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  nth_error ticks offset=Some tick ->LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  nth_error runs program=Some run ->
  Forall(fun event=>namespace_after_fork_event event=true)(skipn(cursor program)(source_events run)) ->
  descriptor_object_frame(namespace_table(worlds program))(physical_tick_table tick
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run)))).
Proof.
  intros RUN SELECTED SOURCE PROGRAM EVENTS.
  destruct(nth_error_split _ _ SELECTED)as[prefix[suffix[TICKS OFFSET]]];subst ticks.
  destruct(source_table_schedule_split _ _ _ _ _ _ _ _ RUN)as[middle[middle_worlds[PREFIX REMAINING]]].
  inversion REMAINING as[|before before_worlds selected next next_worlds rest after after_worlds STEP TAIL];subst.
  destruct(source_table_step_selected _ _ _ _ _ _ _ _ _ STEP SOURCE)
    as[actual[event[snapshot[ACTUAL[EVENT[PRIMITIVE[BEFORE AFTER]]]]]]].
  assert(SAME:actual=run)by congruence;subst actual.
  assert(LOCAL:namespace_kernel_steps(worlds program)(source_program_events runs program prefix)(middle_worlds program)).
  { eapply source_table_schedule_projects;[|exact PREFIX].
    intros actor observed selected point ACTUAL_STEP;eapply source_primitive_namespace;exact ACTUAL_STEP. }
  pose proof(source_table_schedule_program_events _ _ _ _ _ _ _ _ _ PREFIX PROGRAM)as CONSUMED.
  assert(FRAME:descriptor_object_frame(namespace_table(worlds program))(namespace_table(middle_worlds program))).
  { eapply namespace_after_fork_object_frame;[|exact LOCAL].
    rewrite CONSUMED;apply source_ownership_firstn;exact EVENTS. }
  intros fd binding PRESENT;rewrite(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE fd),BEFORE in PRESENT.
  exact(FRAME _ _ PRESENT).
Qed.

Theorem source_table_selected_unique_parent operation groups child runs cursor worlds ticks final final_worlds
    offset tick program ordinal run channel peer:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  nth_error ticks offset=Some tick ->LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  nth_error runs program=Some run ->
  Forall(fun event=>namespace_after_fork_event event=true)(skipn(cursor program)(source_events run)) ->
  unique_parent_endpoint(namespace_table(worlds program))channel peer ->
  unique_parent_endpoint(physical_tick_table tick
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run))))channel peer.
Proof.
  intros RUN SELECTED SOURCE PROGRAM EVENTS UNIQUE.
  destruct(nth_error_split _ _ SELECTED)as[prefix[suffix[TICKS OFFSET]]];subst ticks.
  destruct(source_table_schedule_split _ _ _ _ _ _ _ _ RUN)as[middle[middle_worlds[PREFIX REMAINING]]].
  inversion REMAINING as[|before before_worlds selected next next_worlds rest after after_worlds STEP TAIL];subst.
  destruct(source_table_step_selected _ _ _ _ _ _ _ _ _ STEP SOURCE)
    as[actual[event[snapshot[ACTUAL[EVENT[PRIMITIVE[BEFORE AFTER]]]]]]].
  assert(SAME:actual=run)by congruence;subst actual.
  assert(LOCAL:namespace_kernel_steps(worlds program)(source_program_events runs program prefix)(middle_worlds program)).
  { eapply source_table_schedule_projects;[|exact PREFIX].
    intros actor observed selected point ACTUAL_STEP;eapply source_primitive_namespace;exact ACTUAL_STEP. }
  pose proof(source_table_schedule_program_events _ _ _ _ _ _ _ _ _ PREFIX PROGRAM)as CONSUMED.
  assert(FRAME:descriptor_object_frame(namespace_table(worlds program))(namespace_table(middle_worlds program))).
  { eapply namespace_after_fork_object_frame;[|exact LOCAL].
    rewrite CONSUMED;apply source_ownership_firstn;exact EVENTS. }
  pose proof(descriptor_frame_preserves_unique_parent _ _ _ _ FRAME UNIQUE)as MIDDLE.
  intros fd binding PRESENT OBJECT;rewrite(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE fd),BEFORE in PRESENT.
  eapply MIDDLE;eassumption.
Qed.

Theorem source_table_selected_slot_exclusion operation groups child runs cursor worlds ticks final final_worlds
    offset tick program ordinal run channel fd:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  nth_error ticks offset=Some tick ->LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  nth_error runs program=Some run ->
  Forall(fun event=>namespace_after_fork_event event=true)(skipn(cursor program)(source_events run)) ->
  excludes_parent_at(namespace_table(worlds program))channel fd ->
  excludes_parent_at(physical_tick_table tick
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run))))channel fd.
Proof.
  intros RUN SELECTED SOURCE PROGRAM EVENTS EXCLUDED.
  destruct(nth_error_split _ _ SELECTED)as[prefix[suffix[TICKS OFFSET]]];subst ticks.
  destruct(source_table_schedule_split _ _ _ _ _ _ _ _ RUN)as[middle[middle_worlds[PREFIX REMAINING]]].
  inversion REMAINING as[|before before_worlds selected next next_worlds rest after after_worlds STEP TAIL];subst.
  destruct(source_table_step_selected _ _ _ _ _ _ _ _ _ STEP SOURCE)
    as[actual[event[snapshot[ACTUAL[EVENT[PRIMITIVE[BEFORE AFTER]]]]]]].
  assert(SAME:actual=run)by congruence;subst actual.
  assert(LOCAL:namespace_kernel_steps(worlds program)(source_program_events runs program prefix)(middle_worlds program)).
  { eapply source_table_schedule_projects;[|exact PREFIX].
    intros actor observed selected point ACTUAL_STEP;eapply source_primitive_namespace;exact ACTUAL_STEP. }
  pose proof(source_table_schedule_program_events _ _ _ _ _ _ _ _ _ PREFIX PROGRAM)as CONSUMED.
  assert(FRAME:descriptor_object_frame(namespace_table(worlds program))(namespace_table(middle_worlds program))).
  { eapply namespace_after_fork_object_frame;[|exact LOCAL].
    rewrite CONSUMED;apply source_ownership_firstn;exact EVENTS. }
  pose proof(descriptor_frame_preserves_exclusion _ _ _ _ FRAME EXCLUDED)as MIDDLE.
  intros binding PRESENT OBJECT;rewrite(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE fd),BEFORE in PRESENT.
  eapply MIDDLE;eassumption.
Qed.

Theorem actual_task_key_injective left right:
  nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey left)=
    nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey right) ->left=right.
Proof.
  intro SAME;rewrite !physical_identity_key_exact in SAME.
  pose proof(physical_identity_pid_range left)as LEFT;pose proof(physical_identity_pid_range right)as RIGHT.
  change(1<=Z.of_nat(physical_identity_pid left)<=2147483647)%Z in LEFT.
  change(1<=Z.of_nat(physical_identity_pid right)<=2147483647)%Z in RIGHT.
  apply(f_equal Z.of_nat)in SAME;rewrite !Nat2Z.inj_add,!Nat2Z.inj_mul in SAME.
  rewrite Z2Nat.id in SAME by lia.
  change(Z.of_nat(physical_identity_incarnation left)*2147483648+Z.of_nat(physical_identity_pid left)=
    Z.of_nat(physical_identity_incarnation right)*2147483648+Z.of_nat(physical_identity_pid right))%Z in SAME.
  assert(INC:physical_identity_incarnation left=physical_identity_incarnation right)by(apply Nat2Z.inj;lia).
  assert(PID:physical_identity_pid left=physical_identity_pid right)by(apply Nat2Z.inj;lia).
  apply source_physical_identity_injective;unfold physical_identity_task;rewrite INC,PID;reflexivity.
Qed.

Theorem actual_source_program_for_key runs parent program selected run:
  SourceProgramOwner runs parent program ->nth_error runs selected=Some run ->
  nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run))=
    nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey parent) ->selected=program.
Proof.
  intros OWNER PROGRAM SAME;apply actual_task_key_injective in SAME.
  eapply source_owner_unique;eassumption.
Qed.
