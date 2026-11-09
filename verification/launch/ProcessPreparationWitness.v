(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Bind useful private-channel birth to the actual source prefix. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessSourceTables ProcessLaunchWitness ProcessLaunchRecordingWitness
  ProcessParentRecordingWitness ProcessCapabilityRecording ProcessCapabilityBirth.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespacePaths NamespaceKernel NamespaceWorldTrace NamespacePhysical
  NamespaceDescriptorFrame NamespaceForkWitness NamespaceForkWorldWitness NamespaceCapabilities.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Definition preparation_context namespace_id:=
  source_recording_context launch_recording_owner false task_running Int64.zero namespace_id None.

Definition preparation_tables(namespace:NamespaceWorld)(key:nat):DescriptorTable:=
  if Nat.eqb key 1 then namespace_table namespace
  else if Nat.eqb key 3 then fork_fixture_other else fun _=>None.

Definition preparation_tick program ordinal namespace_id namespace event:=
  source_recording_tick launch_recording_owner program ordinal(preparation_context namespace_id)
    (preparation_context namespace_id)launch_before_fork event(preparation_tables namespace).

Lemma preparation_process_view namespace_id:
  SourceProcessView launch_before_fork physical_child(preparation_context namespace_id).
Proof. apply source_recording_context_view;reflexivity. Qed.

Lemma preparation_table_here namespace:
  preparation_tables namespace(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_owner))=
    namespace_table namespace.
Proof. rewrite launch_recording_owner_key;reflexivity. Qed.

Lemma preparation_file_endpoint namespace fd channel side:
  SourceFileView launch_group_objects launch_before_fork physical_parent namespace ->
  launch_parent_files physical_parent fd=None ->
  SourceFileView launch_group_objects launch_before_fork physical_parent
    (namespace_retable namespace(table_put(namespace_table namespace)fd(endpoint_binding channel side))).
Proof.
  intros VIEW FREE query group;change(launch_parent_files physical_parent query=Some group <->
    exists binding object,table_put(namespace_table namespace)fd(endpoint_binding channel side)query=Some binding /\
      descriptor_object binding=ordinary_object object /\launch_group_objects object=Some group).
  unfold table_put;destruct(Int.eq query fd)eqn:SAME.
  - apply Int.same_if_eq in SAME;subst query;rewrite FREE;split;
      [discriminate|intros[binding[object[PRESENT[OBJECT CLASS]]]];inversion PRESENT;subst binding;discriminate OBJECT].
  - exact(VIEW query group).
Qed.

Lemma preparation_file_remove namespace fd:
  SourceFileView launch_group_objects launch_before_fork physical_parent namespace ->
  launch_parent_files physical_parent fd=None ->
  SourceFileView launch_group_objects launch_before_fork physical_parent
    (namespace_retable namespace(table_remove(namespace_table namespace)fd)).
Proof.
  intros VIEW FREE query group;change(launch_parent_files physical_parent query=Some group <->
    exists binding object,table_remove(namespace_table namespace)fd query=Some binding /\
      descriptor_object binding=ordinary_object object /\launch_group_objects object=Some group).
  unfold table_remove;destruct(Int.eq query fd)eqn:SAME.
  - apply Int.same_if_eq in SAME;subst query;rewrite FREE;split;
      [discriminate|intros[binding[object[PRESENT REST]]];discriminate].
  - exact(VIEW query group).
Qed.

Lemma preparation_ordinary_unique fd binding:
  fork_fixture_ordinary fd=Some binding ->descriptor_object binding=ordinary_object 103 ->fd=Int.repr 7.
Proof.
  intros PRESENT OBJECT;unfold fork_fixture_ordinary in PRESENT.
  destruct(Z.leb 0(Int.signed fd)&&Z.leb(Int.signed fd)8)eqn:BOUNDS;[|discriminate].
  inversion PRESENT;subst binding;cbn[descriptor_object]in OBJECT.
  destruct(Int.eq fd Int.zero||Int.eq fd(Int.repr 2));[discriminate|].
  injection OBJECT as NUMBER.
  apply andb_true_iff in BOUNDS as[LOW HIGH];apply Z.leb_le in LOW,HIGH.
  assert(SIGNED:Int.signed fd=7).
  { assert(SMALL:Z.to_nat(Int.signed fd)=7%nat)by lia.
    apply(f_equal Z.of_nat)in SMALL;rewrite Z2Nat.id in SMALL by exact LOW;exact SMALL. }
  rewrite <-(Int.repr_signed fd),SIGNED;reflexivity.
Qed.

Lemma preparation_initial_files:
  SourceFileView launch_group_objects launch_before_fork physical_parent fork_fixture_initial.
Proof.
  intros fd group;change(launch_parent_files physical_parent fd=Some group <->
    exists binding object,fork_fixture_ordinary fd=Some binding /\
      descriptor_object binding=ordinary_object object /\launch_group_objects object=Some group).
  unfold launch_parent_files;rewrite launch_task_eq_same;cbn[andb];split.
  - destruct(Int.eq fd(Int.repr 7))eqn:SELECTED;[|discriminate].
    intro FILE;inversion FILE;subst group;apply Int.same_if_eq in SELECTED;subst fd.
    exists{|descriptor_object:=ordinary_object 103;descriptor_cloexec:=true|},103%nat;repeat split;reflexivity.
  - intros[binding[object[PRESENT[OBJECT CLASS]]]].
    unfold launch_group_objects in CLASS;destruct(Nat.eqb object 103)eqn:SELECTED;[|discriminate].
    apply Nat.eqb_eq in SELECTED;subst object;inversion CLASS;subst group.
    pose proof(preparation_ordinary_unique _ _ PRESENT OBJECT)as SAME;subst fd;rewrite Int.eq_true;reflexivity.
Qed.

Lemma preparation_nonnegative_put table fd binding:
  launch_nonnegative_table table ->0<=Int.signed fd ->launch_nonnegative_table(table_put table fd binding).
Proof.
  intros VALID NUMBER query present PRESENT;unfold table_put in PRESENT.
  destruct(Int.eq query fd)eqn:SAME;[apply Int.same_if_eq in SAME;subst query;exact NUMBER|eapply VALID;exact PRESENT].
Qed.

Lemma preparation_nonnegative_remove table fd:
  launch_nonnegative_table table ->launch_nonnegative_table(table_remove table fd).
Proof.
  intros VALID query present PRESENT;unfold table_remove in PRESENT.
  destruct(Int.eq query fd);[discriminate|eapply VALID;exact PRESENT].
Qed.

Lemma preparation_initial_nonnegative:launch_nonnegative_table(namespace_table fork_fixture_initial).
Proof.
  intros fd binding PRESENT;change(fork_fixture_ordinary fd=Some binding)in PRESENT.
  unfold fork_fixture_ordinary in PRESENT.
  destruct(Z.leb 0(Int.signed fd)&&Z.leb(Int.signed fd)8)eqn:BOUNDS;[|discriminate].
  apply andb_true_iff in BOUNDS as[LOW HIGH];apply Z.leb_le;exact LOW.
Qed.

(* This chain records namespace snapshots at each common source operation.
   File classification and nonnegative ABI descriptors are checked locally. *)
Inductive PreparationNamespace:NamespaceWorld->list namespace_event->NamespaceWorld->Prop:=
| preparation_namespace_done:forall namespace,
    SourceFileView launch_group_objects launch_before_fork physical_parent namespace ->
    launch_nonnegative_table(namespace_table namespace) ->
    PreparationNamespace namespace[]namespace
| preparation_namespace_next:forall namespace event next events final,
    SourceFileView launch_group_objects launch_before_fork physical_parent namespace ->
    launch_nonnegative_table(namespace_table namespace) ->
    namespace_kernel_event namespace event next ->
    (forall original,event=namespace_process original ->launch_operation physical_parent launch_before_fork original launch_before_fork) ->
    PreparationNamespace next events final ->PreparationNamespace namespace(event::events)final.

Lemma preparation_namespace_initial namespace events final:
  PreparationNamespace namespace events final ->
  SourceFileView launch_group_objects launch_before_fork physical_parent namespace /\
    launch_nonnegative_table(namespace_table namespace).
Proof. intro RUN;inversion RUN;auto. Qed.

Definition preparation_not_fork event:=
  (forall returned,event<>namespace_forked returned)/\event<>namespace_fork_lost.

Lemma preparation_namespace_task namespace event next:
  namespace_kernel_event namespace event next ->
  preparation_not_fork event ->namespace_task next=namespace_task namespace.
Proof.
  intros STEP[NOFORK NOLOSS];inversion STEP;subst;try reflexivity.
  all:try(unfold namespace_default_action;destruct(Int.eq signal(Int.repr 17));reflexivity).
  all:exfalso;first[eapply NOFORK;reflexivity|apply NOLOSS;reflexivity].
Qed.

Inductive PreparationRecording(program namespace_id:nat):
    nat->NamespaceWorld->list namespace_event->list LeanCage_Entry_CallerPhysical_Tick->NamespaceWorld->Prop:=
| preparation_recording_done:forall ordinal namespace,PreparationRecording program namespace_id ordinal namespace[][]namespace
| preparation_recording_next:forall ordinal namespace event next events ticks final,
    SourcePrimitive launch_operation launch_group_objects launch_recording_child launch_recording_owner event
      (preparation_tick program ordinal namespace_id namespace event)
      {|source_process_before:=launch_before_fork;source_process_after:=launch_before_fork;
        source_namespace_before:=namespace;source_namespace_after:=next|} ->
    PreparationRecording program namespace_id(S ordinal)next events ticks final ->
    PreparationRecording program namespace_id ordinal namespace(event::events)
      (preparation_tick program ordinal namespace_id namespace event::ticks)final.

Theorem preparation_namespace_recording namespace events final:
  PreparationNamespace namespace events final ->
  namespace_task namespace=physical_parent ->
  Forall preparation_not_fork events ->
  forall program namespace_id ordinal,exists ticks,PreparationRecording program namespace_id ordinal namespace events ticks final.
Proof.
  intro RUN;induction RUN;intros TASK NOFORK program namespace_id ordinal.
  - exists[];constructor.
  - inversion NOFORK as[|actual rest HEAD TAIL];subst actual rest.
    assert(NEXT_TASK:namespace_task next=physical_parent).
    { rewrite(preparation_namespace_task _ _ _ H1 HEAD);exact TASK. }
    destruct(IHRUN NEXT_TASK TAIL program namespace_id(S ordinal))as[ticks REST].
    eexists;eapply preparation_recording_next with(next:=next);[|exact REST].
    unfold preparation_tick;eapply source_recording_primitive with(snapshot:={|
      source_process_before:=launch_before_fork;source_process_after:=launch_before_fork;
      source_namespace_before:=namespace;source_namespace_after:=next|}).
    + rewrite launch_recording_owner_task;exact TASK.
    + rewrite launch_recording_owner_task;discriminate.
    + rewrite launch_recording_child_task;apply preparation_process_view.
    + rewrite launch_recording_child_task;apply preparation_process_view.
    + exact H1.
    + intros original SAME;rewrite launch_recording_owner_task;apply H2;exact SAME.
    + apply preparation_table_here.
    + exact H0.
    + rewrite launch_recording_owner_task;exact H.
    + rewrite launch_recording_owner_task;exact(proj1(preparation_namespace_initial _ _ _ RUN)).
Qed.

Theorem preparation_recording_program program namespace_id ordinal namespace events ticks final:
  PreparationRecording program namespace_id ordinal namespace events ticks final ->
  ProgramRecording(SourcePrimitive launch_operation launch_group_objects launch_recording_child)
    launch_recording_owner program ordinal namespace events ticks final.
Proof.
  intro RUN;induction RUN.
  - apply program_recording_done.
  - eapply program_recording_next with(snapshot:={|source_process_before:=launch_before_fork;
      source_process_after:=launch_before_fork;source_namespace_before:=namespace;source_namespace_after:=next|});
      [reflexivity|exact H|exact IHRUN].
Qed.

Definition preparation_paired_world:=namespace_retable fork_fixture_initial fork_fixture_paired.
Definition preparation_duplicated_world:=namespace_retable preparation_paired_world fork_fixture_duplicated.
Definition preparation_closed_world:=namespace_retable preparation_duplicated_world fork_fixture_inherited.
Definition preparation_masked_world:=namespace_remask preparation_closed_world(namespace_blockable_mask Int64.mone).

Lemma preparation_paired_files:
  SourceFileView launch_group_objects launch_before_fork physical_parent preparation_paired_world.
Proof.
  pose proof(preparation_file_endpoint fork_fixture_initial(Int.repr 9)60 parent_endpoint
    preparation_initial_files(Logic.eq_refl _))as FIRST.
  exact(preparation_file_endpoint(namespace_retable fork_fixture_initial
    (table_put fork_fixture_ordinary(Int.repr 9)(endpoint_binding 60 parent_endpoint)))
    (Int.repr 10)60 child_endpoint FIRST(Logic.eq_refl _)).
Qed.
Lemma preparation_duplicated_files:
  SourceFileView launch_group_objects launch_before_fork physical_parent preparation_duplicated_world.
Proof.
  exact(preparation_file_endpoint preparation_paired_world(Int.repr 60)60 child_endpoint
    preparation_paired_files(Logic.eq_refl _)).
Qed.
Lemma preparation_closed_files:
  SourceFileView launch_group_objects launch_before_fork physical_parent preparation_closed_world.
Proof.
  exact(preparation_file_remove preparation_duplicated_world(Int.repr 10)preparation_duplicated_files(Logic.eq_refl _)).
Qed.
Lemma preparation_masked_files:
  SourceFileView launch_group_objects launch_before_fork physical_parent preparation_masked_world.
Proof. exact preparation_closed_files. Qed.
Lemma preparation_fork_files:
  SourceFileView launch_group_objects launch_before_fork physical_parent fork_fixture_world.
Proof. exact preparation_closed_files. Qed.

Lemma preparation_paired_nonnegative:launch_nonnegative_table(namespace_table preparation_paired_world).
Proof.
  unfold preparation_paired_world;change(launch_nonnegative_table fork_fixture_paired).
  unfold fork_fixture_paired;apply preparation_nonnegative_put;[apply preparation_nonnegative_put;
    [apply preparation_initial_nonnegative|change(0<=9);lia]|change(0<=10);lia].
Qed.
Lemma preparation_duplicated_nonnegative:launch_nonnegative_table(namespace_table preparation_duplicated_world).
Proof.
  change(launch_nonnegative_table fork_fixture_duplicated);unfold fork_fixture_duplicated.
  apply preparation_nonnegative_put;[exact preparation_paired_nonnegative|change(0<=60);lia].
Qed.
Lemma preparation_closed_nonnegative:launch_nonnegative_table(namespace_table preparation_closed_world).
Proof.
  change(launch_nonnegative_table fork_fixture_inherited);unfold fork_fixture_inherited.
  apply preparation_nonnegative_remove;exact preparation_duplicated_nonnegative.
Qed.
Lemma preparation_masked_nonnegative:launch_nonnegative_table(namespace_table preparation_masked_world).
Proof. exact preparation_closed_nonnegative. Qed.

Ltac preparation_useful_files:=first[exact preparation_initial_files|exact preparation_paired_files|
  exact preparation_duplicated_files|exact preparation_closed_files|exact preparation_masked_files|
  exact preparation_fork_files].
Ltac preparation_useful_nonnegative:=first[exact preparation_initial_nonnegative|exact preparation_paired_nonnegative|
  exact preparation_duplicated_nonnegative|exact preparation_closed_nonnegative|exact preparation_masked_nonnegative|
  exact launch_actual_fork_nonnegative].
Ltac preparation_useful_kernel:=first[apply namespace_kernel_source|
  (eapply namespace_kernel_pair_success with(channel:=60%nat)(after:=fork_fixture_paired);
    [exact fork_fixture_pair|apply fork_fixture_ambient_has_no_channel])|
  (eapply namespace_kernel_duplicate_success with(after:=fork_fixture_duplicated);exact fork_fixture_duplicate)|
  (eapply namespace_kernel_close;apply close_table_success)|
  apply namespace_kernel_mask_success|apply namespace_kernel_default_success].

Theorem preparation_actual_common_namespace pair:
  PreparationNamespace fork_fixture_initial
    (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))fork_fixture_world.
Proof.
  unfold namespace_child_common_log;cbn[repeat app].
  repeat first[
    (apply preparation_namespace_done;[preparation_useful_files|preparation_useful_nonnegative])|
    (eapply preparation_namespace_next;
      [preparation_useful_files|preparation_useful_nonnegative|preparation_useful_kernel|
       intros original SAME;try discriminate;inversion SAME;subst original;
         first[(apply launch_neutral;reflexivity)|(apply launch_close_ordinary;reflexivity)]|])].
Qed.

Theorem preparation_actual_common_no_fork pair:
  Forall preparation_not_fork
    (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10)).
Proof.
  unfold namespace_child_common_log;cbn[repeat app].
  repeat first[apply Forall_nil|(apply Forall_cons;[unfold preparation_not_fork;split;intros;discriminate|])].
Qed.

Theorem preparation_actual_common_recording pair program namespace_id:
  exists ticks,PreparationRecording program namespace_id 0 fork_fixture_initial
    (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))ticks fork_fixture_world.
Proof.
  eapply preparation_namespace_recording;[apply preparation_actual_common_namespace|reflexivity|
    apply preparation_actual_common_no_fork].
Qed.

Lemma preparation_ambient_nonnegative:launch_nonnegative_table fork_fixture_other.
Proof.
  intros fd binding PRESENT;unfold fork_fixture_other in PRESENT.
  destruct(Z.leb 0(Int.signed fd)&&Z.leb(Int.signed fd)2)eqn:BOUNDS;[|discriminate].
  apply andb_true_iff in BOUNDS as[LOW HIGH];apply Z.leb_le;exact LOW.
Qed.

Lemma preparation_tables_nonnegative namespace:
  launch_nonnegative_table(namespace_table namespace) ->
  forall actor,launch_nonnegative_table(preparation_tables namespace actor).
Proof.
  intros VALID actor;unfold preparation_tables;destruct(Nat.eqb actor 1);[exact VALID|].
  destruct(Nat.eqb actor 3);[exact preparation_ambient_nonnegative|intros;discriminate].
Qed.

Definition preparation_capabilities namespace:CapabilityWorld:={|
  capability_tables:=preparation_tables namespace;capability_messages:=[]|}.

Lemma preparation_tick_observed program ordinal namespace_id namespace event:
  launch_nonnegative_table(namespace_table namespace) ->
  CapabilityObserved(preparation_tick program ordinal namespace_id namespace event)(preparation_capabilities namespace).
Proof.
  intros VALID actor fd;unfold preparation_tick,preparation_capabilities;cbn[capability_tables].
  symmetry;apply source_recording_table;apply preparation_tables_nonnegative;exact VALID.
Qed.

Lemma preparation_primitive_nonnegative program ordinal namespace_id namespace event next:
  SourcePrimitive launch_operation launch_group_objects launch_recording_child launch_recording_owner event
    (preparation_tick program ordinal namespace_id namespace event)
    {|source_process_before:=launch_before_fork;source_process_after:=launch_before_fork;
      source_namespace_before:=namespace;source_namespace_after:=next|} ->
  launch_nonnegative_table(namespace_table namespace).
Proof.
  intros PRIMITIVE fd binding PRESENT.
  rewrite <-(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE)in PRESENT.
  unfold physical_tick_table in PRESENT;destruct(Z.leb 0(Int.signed fd))eqn:LOW;[apply Z.leb_le;exact LOW|discriminate].
Qed.

Lemma preparation_capabilities_retable namespace next:
  capability_retable(preparation_capabilities namespace)1(namespace_table next)=preparation_capabilities next.
Proof.
  unfold capability_retable,preparation_capabilities;cbn[capability_tables capability_messages].
  f_equal;apply functional_extensionality;intro actor.
  unfold task_table_put,preparation_tables;destruct(Nat.eqb actor 1);reflexivity.
Qed.

Lemma preparation_capabilities_pending namespace:
  capability_pending(preparation_capabilities namespace)[]=preparation_capabilities namespace.
Proof. reflexivity. Qed.

Theorem preparation_recording_capabilities program namespace_id ordinal namespace events ticks final:
  PreparationRecording program namespace_id ordinal namespace events ticks final ->
  Forall(fun event=>namespace_after_fork_event event=true\/namespace_preparation_local event=true)events ->
  forall runs run prefix suffix native metadata external can_acquire,
    nth_error runs program=Some run ->source_actor run=launch_recording_owner ->
    source_events run=prefix++events++suffix ->length prefix=ordinal ->
  CapabilityPreparation launch_operation launch_group_objects runs native metadata external can_acquire
    launch_recording_owner launch_recording_child(preparation_capabilities namespace)ticks(preparation_capabilities final).
Proof.
  intro RUN;induction RUN;intros PROFILE runs run prefix suffix native metadata external can_acquire PROGRAM ACTOR EVENTS LENGTH.
  - constructor.
  - inversion PROFILE as[|actual rest HEAD TAIL];subst actual rest.
    assert(EVENT:nth_error(source_events run)ordinal=Some event).
    { rewrite <-LENGTH,EVENTS;apply recording_head_event. }
    assert(OBSERVED:CapabilityObserved(preparation_tick program ordinal namespace_id namespace event)
      (preparation_capabilities namespace)).
    { apply preparation_tick_observed;eapply preparation_primitive_nonnegative;exact H. }
    assert(AFTER:capability_pending(capability_retable(preparation_capabilities namespace)
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run)))(namespace_table next))[]=
      preparation_capabilities next).
    { rewrite ACTOR,launch_recording_owner_key,preparation_capabilities_retable;reflexivity. }
    assert(REST:CapabilityPreparation launch_operation launch_group_objects runs native metadata external can_acquire
      launch_recording_owner launch_recording_child(preparation_capabilities next)ticks(preparation_capabilities final)).
    { eapply IHRUN with(run:=run)(prefix:=prefix++[event])(suffix:=suffix);try eassumption.
      - rewrite EVENTS;repeat rewrite <-app_assoc;reflexivity.
      - rewrite length_app;cbn;lia. }
    destruct HEAD as[ORDINARY|LOCAL].
    + eapply capability_preparation_recorded with(middle:=preparation_capabilities next);[exact OBSERVED| |exact REST].
      apply recorded_capability_source;eapply source_capability_call with(run:=run)(program:=program)
        (ordinal:=ordinal)(event:=event)(retained:=[])(snapshot:={|
          source_process_before:=launch_before_fork;source_process_after:=launch_before_fork;
          source_namespace_before:=namespace;source_namespace_after:=next|}).
      * exact PROGRAM.
      * exact EVENT.
      * reflexivity.
      * rewrite ACTOR;exact H.
      * exact ORDINARY.
      * exact OBSERVED.
      * apply incl_refl.
      * symmetry;exact AFTER.
    + eapply capability_preparation_local with(middle:=preparation_capabilities next);[exact OBSERVED| |exact REST].
      eapply preparation_capability_call with(run:=run)(program:=program)(ordinal:=ordinal)(event:=event)
        (retained:=[])(snapshot:={|source_process_before:=launch_before_fork;source_process_after:=launch_before_fork;
          source_namespace_before:=namespace;source_namespace_after:=next|}).
      * exact PROGRAM.
      * exact EVENT.
      * reflexivity.
      * rewrite ACTOR;exact H.
      * exact LOCAL.
      * exact OBSERVED.
      * apply incl_refl.
      * symmetry;exact AFTER.
Qed.

Definition preparation_pair_event pair:=namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero pair Ptrofs.zero
  Int.zero(Int.repr 9)(Int.repr 10).
Definition preparation_pair_tail pair:=skipn 9
  (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10)).

Lemma preparation_common_pair_cut pair:
  repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10)=
    repeat namespace_source_event 8++preparation_pair_event pair::preparation_pair_tail pair.
Proof. unfold preparation_pair_tail,preparation_pair_event,namespace_child_common_log;cbn[repeat app skipn];reflexivity. Qed.

Lemma preparation_common_length pair:
  length(repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))=60%nat.
Proof. reflexivity. Qed.
Lemma preparation_pair_tail_length pair:length(preparation_pair_tail pair)=51%nat.
Proof. reflexivity. Qed.

Theorem preparation_actual_pair_tail_namespace pair:
  PreparationNamespace preparation_paired_world(preparation_pair_tail pair)fork_fixture_world.
Proof.
  unfold preparation_pair_tail,namespace_child_common_log;cbn[repeat app skipn].
  repeat first[
    (apply preparation_namespace_done;[preparation_useful_files|preparation_useful_nonnegative])|
    (eapply preparation_namespace_next;
      [preparation_useful_files|preparation_useful_nonnegative|preparation_useful_kernel|
       intros original SAME;try discriminate;inversion SAME;subst original;
         first[(apply launch_neutral;reflexivity)|(apply launch_close_ordinary;reflexivity)]|])].
Qed.

Lemma preparation_actual_pair_tail_profile pair:
  Forall(fun event=>namespace_after_fork_event event=true\/namespace_preparation_local event=true)
    (preparation_pair_tail pair).
Proof.
  unfold preparation_pair_tail,namespace_child_common_log;cbn[repeat app skipn].
  repeat first[apply Forall_nil|(apply Forall_cons;[first[left;reflexivity|right;reflexivity]|])].
Qed.

Lemma preparation_actual_pair_tail_no_fork pair:
  Forall preparation_not_fork(preparation_pair_tail pair).
Proof.
  unfold preparation_pair_tail,namespace_child_common_log;cbn[repeat app skipn].
  repeat first[apply Forall_nil|(apply Forall_cons;[unfold preparation_not_fork;split;intros;discriminate|])].
Qed.

Theorem preparation_actual_pair_primitive pair program namespace_id:
  SourcePrimitive launch_operation launch_group_objects launch_recording_child launch_recording_owner
    (preparation_pair_event pair)(preparation_tick program 8 namespace_id fork_fixture_initial(preparation_pair_event pair))
    {|source_process_before:=launch_before_fork;source_process_after:=launch_before_fork;
      source_namespace_before:=fork_fixture_initial;source_namespace_after:=preparation_paired_world|}.
Proof.
  unfold preparation_tick;eapply source_recording_primitive with(snapshot:={|
    source_process_before:=launch_before_fork;source_process_after:=launch_before_fork;
    source_namespace_before:=fork_fixture_initial;source_namespace_after:=preparation_paired_world|}).
  - rewrite launch_recording_owner_task;reflexivity.
  - rewrite launch_recording_owner_task;discriminate.
  - rewrite launch_recording_child_task;apply preparation_process_view.
  - rewrite launch_recording_child_task;apply preparation_process_view.
  - eapply namespace_kernel_pair_success with(channel:=60%nat);[exact fork_fixture_pair|apply fork_fixture_ambient_has_no_channel].
  - intros original SAME;discriminate.
  - apply preparation_table_here.
  - exact preparation_initial_nonnegative.
  - rewrite launch_recording_owner_task;exact preparation_initial_files.
  - rewrite launch_recording_owner_task;exact preparation_paired_files.
Qed.

Lemma preparation_initial_channel_absent channel:
  forall actor,channel_absent(preparation_tables fork_fixture_initial actor)channel.
Proof.
  intro actor;unfold preparation_tables;destruct(Nat.eqb actor 1);[apply fork_fixture_ordinary_has_no_channel|].
  destruct(Nat.eqb actor 3);[|intros;discriminate].
  pose proof(fork_fixture_ambient_has_no_channel channel)as ABSENT;inversion ABSENT;assumption.
Qed.

Lemma preparation_actual_pair_capabilities:
  pair_capability_model(preparation_capabilities fork_fixture_initial)1%nat(Int.repr 9)(Int.repr 10)60%nat
    fork_fixture_paired(preparation_capabilities preparation_paired_world).
Proof.
  rewrite <-(preparation_capabilities_retable fork_fixture_initial preparation_paired_world).
  apply pair_capability_created.
  - exact fork_fixture_pair.
  - apply preparation_initial_channel_absent.
  - constructor.
Qed.

Definition launch_fork_capabilities:=capability_retable(preparation_capabilities fork_fixture_world)2 fork_fixture_inherited.

Theorem preparation_actual_fork_primitive program namespace_id:
  SourcePrimitive launch_operation launch_group_objects launch_recording_child launch_recording_owner
    (namespace_forked(Int.repr 2))(preparation_tick program 60 namespace_id fork_fixture_world(namespace_forked(Int.repr 2)))
    {|source_process_before:=launch_before_fork;
      source_process_after:=launch_world launch_fork_files None task_running Int64.zero None;
      source_namespace_before:=fork_fixture_world;source_namespace_after:=fork_fixture_world|}.
Proof.
  unfold preparation_tick;eapply source_recording_primitive with(snapshot:={|
    source_process_before:=launch_before_fork;
    source_process_after:=launch_world launch_fork_files None task_running Int64.zero None;
    source_namespace_before:=fork_fixture_world;source_namespace_after:=fork_fixture_world|}).
  - rewrite launch_recording_owner_task;reflexivity.
  - rewrite launch_recording_owner_task;discriminate.
  - rewrite launch_recording_child_task;apply preparation_process_view.
  - rewrite launch_recording_child_task;apply source_recording_context_view;reflexivity.
  - apply namespace_kernel_fork_success with(snapshot:=fork_fixture_snapshot);apply namespace_fork_parent_effect;
      repeat split;reflexivity.
  - intros original SAME;discriminate.
  - apply preparation_table_here.
  - exact launch_actual_fork_nonnegative.
  - rewrite launch_recording_owner_task;exact preparation_fork_files.
  - rewrite launch_recording_owner_task;exact launch_actual_fork_file_view.
Qed.

Lemma preparation_actual_fork_capabilities:
  fork_capability_model(preparation_capabilities fork_fixture_world)1%nat 2%nat fork_fixture_inherited launch_fork_capabilities.
Proof. apply fork_capability_copied;reflexivity. Qed.

Theorem preparation_actual_capability_birth runs run program(namespace_id:nat)pair parent_tail native metadata external can_acquire:
  nth_error runs program=Some run ->source_actor run=launch_recording_owner ->
  source_events run=(repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))++
    namespace_forked(Int.repr 2)::parent_tail ->
  CapabilityBirth launch_operation launch_group_objects runs native metadata external can_acquire
    launch_recording_owner launch_recording_child pair_capability_model fork_capability_model fork_fixture_snapshot
    program 60 launch_fork_capabilities.
Proof.
  intros PROGRAM ACTOR EVENTS.
  destruct(preparation_namespace_recording _ _ _(preparation_actual_pair_tail_namespace pair)
    (Logic.eq_refl _)(preparation_actual_pair_tail_no_fork pair)program namespace_id 9)as[ticks RECORDING].
  set(prefix:=repeat namespace_source_event 8++[preparation_pair_event pair]).
  assert(TAIL_EVENTS:source_events run=prefix++preparation_pair_tail pair++namespace_forked(Int.repr 2)::parent_tail).
  { rewrite EVENTS,preparation_common_pair_cut;unfold prefix;repeat rewrite <-app_assoc;reflexivity. }
  assert(PREFIX_LENGTH:length prefix=9%nat)by reflexivity.
  pose proof(preparation_recording_program _ _ _ _ _ _ _ RECORDING)as TABLE_RECORDING.
  set(cursor:=fun query=>if Nat.eqb query program then 9%nat else 0%nat).
  destruct(program_recording_tables _ _ _ _ _ _ _ _ TABLE_RECORDING runs run prefix
    (namespace_forked(Int.repr 2)::parent_tail)cursor(fun _=>preparation_paired_world)
    PROGRAM ACTOR TAIL_EVENTS PREFIX_LENGTH)as[final[worlds[ORDER[FINAL[WORLD FRAME]]]]].
  - unfold cursor;rewrite Nat.eqb_refl;reflexivity.
  - reflexivity.
  - eapply capability_birth with(before:=preparation_capabilities fork_fixture_initial)
      (paired:=preparation_capabilities preparation_paired_world)(beforeFork:=preparation_capabilities fork_fixture_world)
      (preparation:=ticks)(pairOrdinal:=8%nat)(forkOrdinal:=60%nat)(firstCursor:=cursor)(finalCursor:=final).
    + eapply source_pair_occurrence with(run:=run)(output:=pair)(offset:=Ptrofs.zero)
        (tick:=preparation_tick program 8 namespace_id fork_fixture_initial(preparation_pair_event pair))
        (snapshot:={|source_process_before:=launch_before_fork;source_process_after:=launch_before_fork;
          source_namespace_before:=fork_fixture_initial;source_namespace_after:=preparation_paired_world|}).
      * exact PROGRAM.
      * exact ACTOR.
      * rewrite EVENTS,preparation_common_pair_cut;reflexivity.
      * reflexivity.
      * apply preparation_actual_pair_primitive.
      * apply preparation_tick_observed;exact preparation_initial_nonnegative.
      * rewrite launch_recording_owner_key;apply preparation_actual_pair_capabilities.
    + eapply preparation_recording_capabilities;[exact RECORDING|apply preparation_actual_pair_tail_profile|
        exact PROGRAM|exact ACTOR|exact TAIL_EVENTS|exact PREFIX_LENGTH].
    + eapply source_table_schedule_erases;exact ORDER.
    + unfold cursor;rewrite Nat.eqb_refl;reflexivity.
    + rewrite FINAL,preparation_pair_tail_length;reflexivity.
    + eapply source_fork_occurrence with(run:=run)
        (tick:=preparation_tick program 60 namespace_id fork_fixture_world(namespace_forked(Int.repr 2)))
        (observation:={|source_process_before:=launch_before_fork;
        source_process_after:=launch_world launch_fork_files None task_running Int64.zero None;
        source_namespace_before:=fork_fixture_world;source_namespace_after:=fork_fixture_world|}).
      * exact PROGRAM.
      * exact ACTOR.
      * rewrite EVENTS;reflexivity.
      * reflexivity.
      * apply preparation_actual_fork_primitive.
      * rewrite launch_recording_owner_task;reflexivity.
      * rewrite launch_recording_child_task;reflexivity.
      * repeat split;reflexivity.
      * apply namespace_fork_parent_effect;repeat split;reflexivity.
      * apply preparation_tick_observed;exact launch_actual_fork_nonnegative.
      * rewrite launch_recording_owner_key.
        assert(CHILD_KEY:nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child)=2%nat).
        { rewrite <-physical_identity_task_key,launch_recording_child_task.
          change((0*Z.to_nat 2147483648+2)%nat=2%nat);reflexivity. }
        rewrite CHILD_KEY;apply preparation_actual_fork_capabilities.
Qed.
