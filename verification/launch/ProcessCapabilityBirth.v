(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Bind socketpair birth and descriptor copying to the actual fork. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine ProcessEffects.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessSourceRecording
  ProcessCapabilityRecording.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace
  NamespaceDescriptorFrame NamespaceCapabilities NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.

Definition PairCapabilityPrimitive:=CapabilityWorld->nat->int->int->nat->DescriptorTable->CapabilityWorld->Prop.

(* The channel key denotes the incarnation of the new anonymous object, not a
   reusable descriptor/inode number. Freshness includes outstanding SCM_RIGHTS
   references. These fields describe one successful socketpair, not a helper. *)
Record PairCapabilityContract(pair:PairCapabilityPrimitive):Prop:={
  pair_capability_table:forall before actor first second channel table after,
    pair before actor first second channel table after ->
    socketpair_table(capability_tables before actor)first second channel table;
  pair_capability_fresh:forall before actor first second channel table after,
    pair before actor first second channel table after ->
    forall query,channel_absent(capability_tables before query)channel;
  pair_capability_pending_fresh:forall before actor first second channel table after,
    pair before actor first second channel table after ->
    Forall(fun message=>forall side,capability_object message<>release_endpoint channel side)
      (capability_messages before);
  pair_capability_tables:forall before actor first second channel table after,
    pair before actor first second channel table after ->
    capability_tables after=task_table_put(capability_tables before)actor table;
  pair_capability_messages:forall before actor first second channel table after,
    pair before actor first second channel table after ->
    incl(capability_messages after)(capability_messages before)
}.

Definition ForkCapabilityPrimitive:=CapabilityWorld->nat->nat->DescriptorTable->CapabilityWorld->Prop.
Record ForkCapabilityContract(fork:ForkCapabilityPrimitive):Prop:={
  fork_capability_inherited:forall before parent child inherited after,
    fork before parent child inherited after ->inherited=capability_tables before parent;
  fork_capability_fresh_task:forall before parent child inherited after,
    fork before parent child inherited after ->forall fd,capability_tables before child fd=None;
  fork_capability_tables:forall before parent child inherited after,
    fork before parent child inherited after ->
    capability_tables after=task_table_put(capability_tables before)child inherited;
  fork_capability_messages:forall before parent child inherited after,
    fork before parent child inherited after ->
    incl(capability_messages after)(capability_messages before)
}.

(* Concrete primitive models retain arbitrary pre-existing foreign descriptors
   and acquisition permissions. Their only successful-pair restriction is the
   kernel's new-object freshness; fork copies exactly the selected parent. *)
Inductive pair_capability_model:PairCapabilityPrimitive:=
| pair_capability_created:forall before actor first second channel table,
    socketpair_table(capability_tables before actor)first second channel table ->
    (forall query,channel_absent(capability_tables before query)channel) ->
    Forall(fun message=>forall side,capability_object message<>release_endpoint channel side)
      (capability_messages before) ->
    pair_capability_model before actor first second channel table(capability_retable before actor table).

Definition pair_capability_linux:PairCapabilityContract pair_capability_model.
Proof.
  constructor;intros before actor first second channel table after OP;inversion OP;subst;
    cbn[capability_retable capability_tables capability_messages];eauto using incl_refl.
Defined.

Inductive fork_capability_model:ForkCapabilityPrimitive:=
| fork_capability_copied:forall before parent child inherited,
    inherited=capability_tables before parent ->(forall fd,capability_tables before child fd=None) ->
    fork_capability_model before parent child inherited(capability_retable before child inherited).

Definition fork_capability_linux:ForkCapabilityContract fork_capability_model.
Proof.
  constructor;intros before parent child inherited after OP;inversion OP;subst;
    cbn[capability_retable capability_tables capability_messages];eauto using incl_refl.
Defined.

Definition namespace_preparation_local event:=match event with
  |namespace_duplicated _ _ _|namespace_duplicate_lost _ _|
   namespace_masked _ _|namespace_mask_lost _|
   namespace_defaulted _ _|namespace_default_lost _=>true
  |_=>false end.

Lemma namespace_preparation_objects_from before event after:
  namespace_preparation_local event=true ->namespace_kernel_event before event after ->
  table_objects_from(namespace_table before)(namespace_table after).
Proof.
  intros PROFILE KERNEL;inversion KERNEL;subst;cbn[namespace_preparation_local]in PROFILE;try discriminate;
    cbn[namespace_retable namespace_remask namespace_table].
  all:try(apply descriptor_frame_objects_from,descriptor_object_frame_refl).
  all:try(eapply local_duplicate_objects_from;eassumption).
  all:try(unfold namespace_default_action;destruct(Int.eq signal(Int.repr 17));
    apply descriptor_frame_objects_from,descriptor_object_frame_refl).
Qed.

Inductive PreparationCapabilityCall operation groups child runs:
    CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityWorld->Prop:=
| preparation_capability_call:forall before tick after run program ordinal event snapshot retained,
    nth_error runs program=Some run ->nth_error(source_events run)ordinal=Some event ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    SourcePrimitive operation groups child(source_actor run)event tick snapshot ->
    namespace_preparation_local event=true ->CapabilityObserved tick before ->
    incl retained(capability_messages before) ->
    after=capability_pending
      (capability_retable before(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run)))
        (namespace_table(source_namespace_after snapshot)))retained ->
    PreparationCapabilityCall operation groups child runs before tick after.

Lemma preparation_capability_effect operation groups child runs can_acquire before tick after:
  PreparationCapabilityCall operation groups child runs before tick after ->
  exists actor,CapabilityEffect can_acquire before(capability_local actor)after.
Proof.
  intros[initial observed final run program ordinal event snapshot retained PROGRAM EVENT REFERENCE
    PRIMITIVE PROFILE OBSERVED LOST AFTER];subst final.
  exists(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run))).
  econstructor;[constructor|exact LOST].
  assert(FROM:table_objects_from(namespace_table(source_namespace_before snapshot))
    (namespace_table(source_namespace_after snapshot))).
  { eapply namespace_preparation_objects_from;[exact PROFILE|eapply source_primitive_namespace;exact PRIMITIVE]. }
  intros fd binding PRESENT;destruct(FROM _ _ PRESENT)as[old[previous[OLD OBJECT]]].
  exists old,previous;split;[|exact OBJECT].
  rewrite OBSERVED,(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE);exact OLD.
Qed.

(* The same actual operation journal, before its local fork. Ordinary source
   steps use the post-fork classifier too; only dup/signal preparation needs an
   extra local rule. Foreign transfer/acquisition remains explicit. *)
Inductive CapabilityPreparation operation groups runs native metadata external can_acquire owner child:
    CapabilityWorld->list LeanCage_Entry_CallerPhysical_Tick->CapabilityWorld->Prop:=
| capability_preparation_done:forall world,
    CapabilityPreparation operation groups runs native metadata external can_acquire owner child world[]world
| capability_preparation_recorded:forall before tick middle ticks after,
    CapabilityObserved tick before ->
    RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick middle ->
    CapabilityPreparation operation groups runs native metadata external can_acquire owner child middle ticks after ->
    CapabilityPreparation operation groups runs native metadata external can_acquire owner child before(tick::ticks)after
| capability_preparation_local:forall before tick middle ticks after,
    CapabilityObserved tick before ->PreparationCapabilityCall operation groups child runs before tick middle ->
    CapabilityPreparation operation groups runs native metadata external can_acquire owner child middle ticks after ->
    CapabilityPreparation operation groups runs native metadata external can_acquire owner child before(tick::ticks)after.

Inductive SourcePairOccurrence operation groups(owner child:LeanCage_Entry_ProcessIdentity)runs
    (pair:PairCapabilityPrimitive)program ordinal:
    CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityWorld->nat->Prop:=
| source_pair_occurrence:forall before tick after channel run output offset first second snapshot,
    nth_error runs program=Some run ->source_actor run=owner ->
    nth_error(source_events run)ordinal=Some
      (namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero output offset Int.zero first second) ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    SourcePrimitive operation groups child owner
      (namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero output offset Int.zero first second)tick snapshot ->
    CapabilityObserved tick before ->
    pair before(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))first second channel
      (namespace_table(source_namespace_after snapshot))after ->
    SourcePairOccurrence operation groups owner child runs pair program ordinal before tick after channel.

Inductive SourceForkOccurrence operation groups(owner child:LeanCage_Entry_ProcessIdentity)runs
    (fork:ForkCapabilityPrimitive)(snapshot:ForkSnapshot)program ordinal:
    CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityWorld->Prop:=
| source_fork_occurrence:forall before tick after run observation,
    nth_error runs program=Some run ->source_actor run=owner ->
    nth_error(source_events run)ordinal=Some(namespace_forked(task_pid(fork_child snapshot))) ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    SourcePrimitive operation groups child owner(namespace_forked(task_pid(fork_child snapshot)))tick observation ->
    fork_parent snapshot=physical_identity_task owner ->fork_child snapshot=physical_identity_task child ->
    fork_matches(source_namespace_before observation)snapshot ->
    namespace_fork_effect(source_namespace_before observation)snapshot(task_pid(fork_child snapshot))
      (source_namespace_after observation) ->
    CapabilityObserved tick before ->
    fork before(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))(fork_inherited_table snapshot)after ->
    SourceForkOccurrence operation groups owner child runs fork snapshot program ordinal before tick after.

Inductive CapabilityBirth operation groups runs native metadata external can_acquire owner child
    pair fork snapshot program channel:CapabilityWorld->Prop:=
| capability_birth:forall before pairTick paired preparation beforeFork forkTick afterFork pairOrdinal forkOrdinal
    firstCursor finalCursor,
    SourcePairOccurrence operation groups owner child runs pair program pairOrdinal before pairTick paired channel ->
    CapabilityPreparation operation groups runs native metadata external can_acquire owner child paired preparation beforeFork ->
    SourceEventSchedule(SourcePrimitive operation groups child)runs firstCursor preparation finalCursor ->
    firstCursor program=S pairOrdinal ->finalCursor program=forkOrdinal ->
    SourceForkOccurrence operation groups owner child runs fork snapshot program forkOrdinal beforeFork forkTick afterFork ->
    CapabilityBirth operation groups runs native metadata external can_acquire owner child
      pair fork snapshot program channel afterFork.

Theorem actual_pair_creates_private pair owner child before first second channel table after:
  PairCapabilityContract pair ->pair before owner first second channel table after ->
  capability_private_invariant owner child channel after.
Proof.
  intros CONTRACT PAIR;split.
  - intros actor[OTHER DIFFERENT];rewrite(pair_capability_tables _ CONTRACT _ _ _ _ _ _ _ PAIR).
    rewrite task_table_put_other by exact OTHER.
    exact(pair_capability_fresh pair CONTRACT before owner first second channel table after PAIR actor).
  - apply Forall_forall;intros message PRESENT.
    pose proof(pair_capability_pending_fresh _ CONTRACT _ _ _ _ _ _ _ PAIR)as FRESH.
    rewrite Forall_forall in FRESH;apply FRESH.
    exact(pair_capability_messages pair CONTRACT before owner first second channel table after PAIR message PRESENT).
Qed.

Theorem actual_fork_preserves_private fork parent child channel before inherited after:
  ForkCapabilityContract fork ->fork before parent child inherited after ->
  capability_private_invariant parent child channel before ->
  capability_private_invariant parent child channel after.
Proof.
  intros CONTRACT FORK[ABSENT MESSAGES];split.
  - intros actor OTHER;rewrite(fork_capability_tables _ CONTRACT _ _ _ _ _ FORK).
    rewrite task_table_put_other by exact(proj2 OTHER);apply ABSENT;exact OTHER.
  - apply Forall_forall;intros message PRESENT;rewrite Forall_forall in MESSAGES;apply MESSAGES.
    exact(fork_capability_messages fork CONTRACT before parent child inherited after FORK message PRESENT).
Qed.

Theorem capability_preparation_preserves_private operation groups runs native metadata external can_acquire owner child
    channel before ticks after:
  NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
  capability_private_invariant(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))channel before ->
  CapabilityPreparation operation groups runs native metadata external can_acquire owner child before ticks after ->
  capability_private_invariant(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))channel after.
Proof.
  intros NATIVE METADATA INITIAL RUN;induction RUN;[exact INITIAL| |].
  - apply IHRUN;eapply recorded_capability_preserves_private;eassumption.
  - apply IHRUN;destruct(preparation_capability_effect _ _ _ _ can_acquire _ _ _ H0)as[actor EFFECT].
    eapply capability_effect_preserves_private with(action:=capability_local actor);
      [exact I|exact I|exact INITIAL|exact EFFECT].
Qed.

Theorem capability_birth_private operation groups runs native metadata external can_acquire owner child
    pair fork snapshot program channel born:
  PairCapabilityContract pair ->ForkCapabilityContract fork ->
  NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
  CapabilityBirth operation groups runs native metadata external can_acquire owner child
    pair fork snapshot program channel born ->
  capability_private_invariant(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))channel born.
Proof.
  intros PAIR FORK NATIVE METADATA BIRTH.
  destruct BIRTH as[before pairTick paired preparation beforeFork forkTick afterFork pairOrdinal forkOrdinal
    firstCursor finalCursor CREATED PREPARATION SCHEDULE FIRST FINAL FORKED].
  inversion CREATED;subst;inversion FORKED;subst.
  eapply actual_fork_preserves_private;[exact FORK|eassumption|].
  eapply capability_preparation_preserves_private;[exact NATIVE|exact METADATA| |exact PREPARATION].
  eapply actual_pair_creates_private;[exact PAIR|eassumption].
Qed.

Theorem capability_birth_foreign_absence operation groups runs native metadata external can_acquire owner child
    pair fork snapshot program channel born ticks after offset tick actor:
  PairCapabilityContract pair ->ForkCapabilityContract fork ->
  NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
  CapabilityBirth operation groups runs native metadata external can_acquire owner child
    pair fork snapshot program channel born ->
  CapabilityHistory operation groups runs native metadata external can_acquire owner child born ticks after ->
  nth_error ticks offset=Some tick ->
  unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))actor ->
  channel_absent(physical_tick_table tick actor)channel.
Proof.
  intros PAIR FORK NATIVE METADATA BIRTH HISTORY SELECTED OTHER.
  eapply capability_history_foreign_absence;[exact NATIVE|exact METADATA| |exact HISTORY|exact SELECTED|exact OTHER].
  eapply capability_birth_private;eassumption.
Qed.
