(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.receipt: Record actual placements and foreign descriptor authority. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessScope ProcessScopeRecording ProcessCgroupRecording ProcessLaunchWitness ProcessLaunchRecordingWitness
  ProcessParentRecordingWitness ProcessChildTickWitness.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespacePhysical NamespaceHandles
  NamespaceSourceOwnership NamespaceSocket NamespaceForkWorldWitness NamespaceCapabilities.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Lemma entry_placement_action actor world event group:
  source_recording_action actor world event=LeanCage_Entry_CallerPhysical_Action_placement group ->
  exists io assigned,namespace_socket_io event=Some io /\IO.operation(source_socket_request io)=writing /\
    process_cgroup_files world(physical_identity_task actor)(IO.descriptor(source_socket_request io))=Some assigned /\
    group=Nat_of_nat assigned.
Proof.
  destruct event;try solve[intro PLACED;discriminate PLACED].
  destruct event;try solve[intro PLACED;discriminate PLACED].
  unfold source_recording_action;destruct(namespace_socket_io(namespace_process(process_entry event)))as[io|]eqn:SOCKET;
    [|intro PLACED;discriminate PLACED].
  destruct(IO.operation(source_socket_request io))eqn:OPERATION;[intro PLACED;discriminate PLACED|].
  destruct(process_cgroup_files world(physical_identity_task actor)(IO.descriptor(source_socket_request io)))as[assigned|]eqn:FILE;
    [|intro PLACED;discriminate PLACED].
  intro PLACED;inversion PLACED;subst group;exists io,assigned;repeat split;assumption.
Qed.

Theorem entry_source_placement_recording operation groups child actor program ordinal before after world event tables snapshot:
  SourcePrimitive operation groups child actor event
    (source_recording_tick actor program ordinal before after world event tables)snapshot ->
  source_process_before snapshot=world ->
  PlacementRecording groups(source_recording_tick actor program ordinal before after world event tables).
Proof.
  intros PRIMITIVE WORLD group PLACED.
  change(source_recording_action actor world event=LeanCage_Entry_CallerPhysical_Action_placement group)in PLACED.
  destruct(entry_placement_action _ _ _ _ PLACED)as[io[assigned[SOCKET[WRITING[FILE GROUP]]]]];subst group.
  pose proof(source_primitive_files_before _ _ _ _ _ _ _ PRIMITIVE)as VIEW;rewrite WORLD in VIEW.
  destruct(proj1(VIEW _ _ )FILE)as[binding[object[PRESENT[OBJECT CLASS]]]].
  exists actor,(IO.descriptor(source_socket_request io)),binding,object,
    (journal_byte_values(source_socket_bytes io)),(journal_lost_value(source_socket_lost io)).
  split.
  - apply source_primitive_write with(snapshot:=snapshot)(operation:=operation)(groups:=groups)(child:=child)(event:=event);
      [exact PRIMITIVE|exact SOCKET|exact WRITING].
  - split;[rewrite(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE);exact PRESENT|].
    split;[exact OBJECT|rewrite nat2Natid;exact CLASS].
Qed.

Theorem entry_parent_placement_recordings groups program namespace_id child_table ordinal namespace world events ticks
    after_namespace after_world:
  ParentRecording groups program namespace_id child_table ordinal namespace world events ticks after_namespace after_world ->
  Forall(PlacementRecording groups)ticks.
Proof.
  intro RUN;induction RUN;[constructor|constructor;[|exact IHRUN]].
  unfold launch_parent_tick;eapply entry_source_placement_recording;[exact H|reflexivity].
Qed.

Theorem entry_child_placement_recordings groups program namespace_id parent_table ordinal namespace world events ticks
    after_namespace after_world:
  ChildRecording groups program namespace_id parent_table ordinal namespace world events ticks after_namespace after_world ->
  Forall(PlacementRecording groups)ticks.
Proof.
  intro RUN;induction RUN;[constructor|constructor;[|exact IHRUN]].
  unfold launch_child_tick;eapply entry_source_placement_recording;[exact H|reflexivity].
Qed.

Lemma entry_ambient_cgroup_absent object group:
  launch_group_objects object=Some group ->object_absent fork_fixture_other(ordinary_object object).
Proof.
  unfold launch_group_objects;destruct(Nat.eqb object 103)eqn:CLASS;[|discriminate].
  apply Nat.eqb_eq in CLASS;subst object;intros GROUP fd binding PRESENT OBJECT.
  unfold fork_fixture_other in PRESENT;destruct(Z.leb 0(Int.signed fd)&&Z.leb(Int.signed fd)2);[|discriminate].
  inversion PRESENT;subst binding;cbn[descriptor_object]in OBJECT;injection OBJECT as NUMBER;lia.
Qed.

Definition entry_foreign_tables actor:DescriptorTable:=
  if Nat.eqb actor 3 then fork_fixture_other else fun _=>None.

Lemma entry_other_key actor:
  unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)) ->
  Nat.eqb(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))1=false /\
    Nat.eqb(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))2=false.
Proof.
  intros[OWNER CHILD];rewrite launch_recording_owner_key in OWNER;rewrite launch_recording_child_key in CHILD.
  split;apply Nat.eqb_neq;assumption.
Qed.

Theorem entry_foreign_cgroup_observation tick actor:
  unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)) ->
  physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))=
    entry_foreign_tables(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)) ->
  forall object group,launch_group_objects object=Some group ->
    object_absent(physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)))(ordinary_object object).
Proof.
  intros OTHER TABLE object group CLASS;rewrite TABLE;unfold entry_foreign_tables.
  destruct(Nat.eqb(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))3);
    [eapply entry_ambient_cgroup_absent;exact CLASS|intros;discriminate].
Qed.

Lemma entry_foreign_table_nonnegative actor:
  launch_nonnegative_table(entry_foreign_tables actor).
Proof.
  unfold entry_foreign_tables;destruct(Nat.eqb actor 3);
    [exact child_recording_ambient_nonnegative|intros;discriminate].
Qed.

Theorem entry_parent_foreign_table program ordinal namespace_id child_table before namespace event after actor:
  unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)) ->
  physical_tick_table(launch_parent_tick program ordinal namespace_id child_table before namespace event after)
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))=
    entry_foreign_tables(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)).
Proof.
  intro OTHER;destruct(entry_other_key _ OTHER)as[NOT_PARENT NOT_CHILD].
  assert(TABLE:launch_parent_tables namespace child_table(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))=
    entry_foreign_tables(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))).
  { unfold launch_parent_tables,entry_foreign_tables;rewrite NOT_PARENT,NOT_CHILD;reflexivity. }
  apply functional_extensionality;intro fd;unfold launch_parent_tick;rewrite source_recording_table.
  - rewrite TABLE;reflexivity.
  - rewrite TABLE;apply entry_foreign_table_nonnegative.
Qed.

Theorem entry_child_foreign_table program ordinal namespace_id parent_table before namespace event after actor:
  unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)) ->
  physical_tick_table(launch_child_tick program ordinal namespace_id parent_table before namespace event after)
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))=
    entry_foreign_tables(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)).
Proof.
  intro OTHER;destruct(entry_other_key _ OTHER)as[NOT_PARENT NOT_CHILD].
  assert(TABLE:launch_child_tables namespace parent_table(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))=
    entry_foreign_tables(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))).
  { unfold launch_child_tables,entry_foreign_tables;rewrite NOT_PARENT,NOT_CHILD;reflexivity. }
  apply functional_extensionality;intro fd;unfold launch_child_tick;rewrite source_recording_table.
  - rewrite TABLE;reflexivity.
  - rewrite TABLE;apply entry_foreign_table_nonnegative.
Qed.

Definition EntryForeignCgroupAbsent tick:=forall actor,
  unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)) ->
  forall object group,launch_group_objects object=Some group ->
    object_absent(physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)))(ordinary_object object).

Theorem entry_parent_foreign_cgroup_observations program namespace_id child_table ordinal namespace world events ticks
    after_namespace after_world:
  ParentRecording launch_group_objects program namespace_id child_table ordinal namespace world events ticks
    after_namespace after_world ->Forall EntryForeignCgroupAbsent ticks.
Proof.
  intro RUN;induction RUN;[constructor|constructor;[|exact IHRUN]].
  intros actor OTHER object group CLASS;eapply entry_foreign_cgroup_observation;
    [exact OTHER|apply entry_parent_foreign_table;exact OTHER|exact CLASS].
Qed.

Theorem entry_child_foreign_cgroup_observations program namespace_id parent_table ordinal namespace world events ticks
    after_namespace after_world:
  ChildRecording launch_group_objects program namespace_id parent_table ordinal namespace world events ticks
    after_namespace after_world ->Forall EntryForeignCgroupAbsent ticks.
Proof.
  intro RUN;induction RUN;[constructor|constructor;[|exact IHRUN]].
  intros actor OTHER object group CLASS;eapply entry_foreign_cgroup_observation;
    [exact OTHER|apply entry_child_foreign_table;exact OTHER|exact CLASS].
Qed.
