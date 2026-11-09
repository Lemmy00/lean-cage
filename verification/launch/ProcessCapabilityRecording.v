(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Update capabilities at the same actual primitive occurrence. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessSourceRecording.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace
  NamespaceDescriptorFrame NamespaceCapabilities NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.

(* Closing a descriptor or losing an IPC acknowledgement can discard queued
   rights in the same kernel operation. The intermediate state below is a
   proof decomposition, not a second application syscall or physical tick. *)
Inductive CapabilityEffect can_acquire before action:CapabilityWorld->Prop:=
| capability_effect:forall changed retained,
    capability_step can_acquire before action changed ->incl retained(capability_messages changed) ->
    CapabilityEffect can_acquire before action(capability_pending changed retained).

Theorem capability_effect_preserves_private can_acquire parent child channel before action after:
  source_acquisition_private parent child action ->source_holders_do_not_export parent child action ->
  capability_private_invariant parent child channel before ->
  CapabilityEffect can_acquire before action after ->capability_private_invariant parent child channel after.
Proof.
  intros ACQUISITION NOEXPORT INITIAL EFFECT;destruct EFFECT as[changed retained STEP LOST].
  assert(MIDDLE:capability_private_invariant parent child channel changed).
  { eapply capability_step_preserves_private_from_action;eassumption. }
  destruct MIDDLE as[ABSENT MESSAGES];split;[exact ABSENT|].
  apply Forall_forall;intros message MEMBER.
  rewrite Forall_forall in MESSAGES;apply MESSAGES;apply LOST;exact MEMBER.
Qed.

Definition CapabilityObserved(tick:LeanCage_Entry_CallerPhysical_Tick)(world:CapabilityWorld):Prop:=
  forall actor fd,capability_tables world actor fd=physical_tick_table tick actor fd.

Lemma capability_source_objects_from operation groups child actor event tick snapshot before:
  SourcePrimitive operation groups child actor event tick snapshot ->
  namespace_after_fork_event event=true ->CapabilityObserved tick before ->
  table_objects_from(capability_tables before(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)))
    (namespace_table(source_namespace_after snapshot)).
Proof.
  intros PRIMITIVE PROFILE OBSERVED.
  assert(FRAME:descriptor_object_frame(namespace_table(source_namespace_before snapshot))
    (namespace_table(source_namespace_after snapshot))).
  { eapply namespace_after_fork_object_frame with(events:=[event]);
      [constructor;[exact PROFILE|constructor]|].
    econstructor;[eapply source_primitive_namespace;exact PRIMITIVE|constructor]. }
  intros fd binding PRESENT;destruct(FRAME _ _ PRESENT)as[previous[OLD OBJECT]].
  exists fd,previous;split;[|exact OBJECT].
  rewrite OBSERVED,(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE);exact OLD.
Qed.

(* The raw source occurrence is fixed by its real program and source cursor.
   The one-operation namespace adapter supplies the actual post table; a
   source closure proof supplies PROFILE, rather than assuming no export. *)
Inductive SourceCapabilityCall operation groups child runs:
    CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityWorld->Prop:=
| source_capability_call:forall before tick after run program ordinal event snapshot retained,
    nth_error runs program=Some run ->nth_error(source_events run)ordinal=Some event ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    SourcePrimitive operation groups child(source_actor run)event tick snapshot ->
    namespace_after_fork_event event=true ->CapabilityObserved tick before ->
    incl retained(capability_messages before) ->
    after=capability_pending
      (capability_retable before(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run)))
        (namespace_table(source_namespace_after snapshot)))retained ->
    SourceCapabilityCall operation groups child runs before tick after.

Theorem source_capability_effect operation groups child runs can_acquire before tick after:
  SourceCapabilityCall operation groups child runs before tick after ->
  exists actor,CapabilityEffect can_acquire before(capability_local actor)after.
Proof.
  intros[initial observed final run program ordinal event snapshot retained PROGRAM EVENT REFERENCE
    PRIMITIVE PROFILE OBSERVED LOST AFTER];subst final.
  exists(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run))).
  econstructor;[constructor;eapply capability_source_objects_from;eassumption|exact LOST].
Qed.

(* These relations name one actual returned FFI operation and its original
   tag/origin, sampled at the same Tick. The Linux FD law is conditional on
   genuine, non-substituted execution. Unsafe and intercepted calls remain
   in the broader relation with arbitrary capability effects. *)
Record NativeCapabilityContract
    (native:nat->ProcessImport.Bool->
      CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityAction->CapabilityWorld->Prop)
    can_acquire(owner child:LeanCage_Entry_ProcessIdentity):Prop:={
  native_capability_effect:forall code origin before tick action after,
    native code origin before tick action after ->CapabilityEffect can_acquire before action after;
  native_capability_local:forall code origin before tick action after,
    native code origin before tick action after ->
    LeanCage_Entry_CallerPhysical_ContextSafe owner(LeanCage_Entry_CallerPhysical_Tick_before tick) ->
    origin=ProcessImport.Bool_true ->
    LeanCage_Entry_CallerPhysical_LocalEntryCode(Nat_of_nat code) ->
    action=capability_local(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))
}.

Record MetadataCapabilityContract
    (metadata:nat->ProcessImport.Bool->
      CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityAction->CapabilityWorld->Prop)
    can_acquire(owner child:LeanCage_Entry_ProcessIdentity):Prop:={
  metadata_capability_effect:forall code origin before tick action after,
    metadata code origin before tick action after ->CapabilityEffect can_acquire before action after;
  metadata_capability_local:forall code origin before tick action after,
    metadata code origin before tick action after ->
    LeanCage_Entry_CallerPhysical_ContextSafe owner(LeanCage_Entry_CallerPhysical_Tick_before tick) ->
    origin=ProcessImport.Bool_true ->(code=0%nat \/code=1%nat \/code=2%nat) ->
    action=capability_local(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)) \/
    action=capability_open(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))
}.

Definition capability_action_actor action:=match action with
  |capability_local actor|capability_open actor|capability_fork actor _|capability_send actor _ _|
    capability_receive actor _|capability_acquire actor _ _ _=>Some actor
  |capability_drop=>None end.
Definition ExternalCapabilityActor parent child action:Prop:=forall actor,
  capability_action_actor action=Some actor ->unrelated parent child actor.

Lemma external_capability_no_export parent child action:
  ExternalCapabilityActor parent child action ->source_holders_do_not_export parent child action.
Proof. intro ACTOR;destruct action;try exact I;apply ACTOR;reflexivity. Qed.

Inductive RecordedCapabilityStep operation groups runs
    (native metadata:nat->ProcessImport.Bool->CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->
      CapabilityAction->CapabilityWorld->Prop)
    (external:CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityAction->CapabilityWorld->Prop)
    (can_acquire:nat->nat->Prop)
    (owner child:LeanCage_Entry_ProcessIdentity):
    CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityWorld->Prop:=
| recorded_capability_source:forall before tick after,
    SourceCapabilityCall operation groups child runs before tick after ->
    RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick after
| recorded_capability_native:forall before tick after code origin action,
    native code origin before tick action after ->
    LeanCage_Entry_CallerPhysical_ContextSafe owner(LeanCage_Entry_CallerPhysical_Tick_before tick) ->
    origin=ProcessImport.Bool_true ->
    LeanCage_Entry_CallerPhysical_LocalEntryCode(Nat_of_nat code) ->
    RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick after
| recorded_capability_metadata:forall before tick after code origin action,
    metadata code origin before tick action after ->
    LeanCage_Entry_CallerPhysical_ContextSafe owner(LeanCage_Entry_CallerPhysical_Tick_before tick) ->
    origin=ProcessImport.Bool_true ->(code=0%nat \/code=1%nat \/code=2%nat) ->
    RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick after
| recorded_capability_external:forall before tick after action,
    external before tick action after ->CapabilityEffect can_acquire before action after ->
    ExternalCapabilityActor(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))action ->
    source_acquisition_private(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))action ->
    RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick after
| recorded_capability_parent_exit:forall before tick after,
    LeanCage_Entry_CallerPhysical_Tick_action tick=LeanCage_Entry_CallerPhysical_Action_parentDeath ->
    CapabilityEffect can_acquire before
      (capability_local(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner)))after ->
    RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick after
| recorded_capability_child_exit:forall before tick after,
    LeanCage_Entry_CallerPhysical_Tick_action tick=LeanCage_Entry_CallerPhysical_Action_childDeath ->
    CapabilityEffect can_acquire before
      (capability_local(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)))after ->
    RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick after.

Theorem recorded_capability_preserves_private operation groups runs native metadata external can_acquire owner child
    channel before tick after:
  NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
  capability_private_invariant(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))channel before ->
  RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick after ->
  capability_private_invariant(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))channel after.
Proof.
  intros NATIVE METADATA INITIAL STEP;destruct STEP.
  - destruct(source_capability_effect _ _ _ _ can_acquire _ _ _ H)as[actor EFFECT].
    eapply capability_effect_preserves_private with(action:=capability_local actor);
      [exact I|exact I|exact INITIAL|exact EFFECT].
  - pose proof(native_capability_effect native can_acquire owner child NATIVE _ _ _ _ _ _ H)as EFFECT.
    pose proof(native_capability_local native can_acquire owner child NATIVE _ _ _ _ _ _ H H0 H1 H2)as LOCAL.
    rewrite LOCAL in EFFECT;eapply capability_effect_preserves_private with
      (action:=capability_local(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)));
      [exact I|exact I|exact INITIAL|exact EFFECT].
  - pose proof(metadata_capability_effect metadata can_acquire owner child METADATA _ _ _ _ _ _ H)as EFFECT.
    destruct(metadata_capability_local metadata can_acquire owner child METADATA _ _ _ _ _ _ H H0 H1 H2)as[LOCAL|OPEN].
    + rewrite LOCAL in EFFECT;eapply capability_effect_preserves_private with
        (action:=capability_local(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)));
        [exact I|exact I|exact INITIAL|exact EFFECT].
    + rewrite OPEN in EFFECT;eapply capability_effect_preserves_private with
        (action:=capability_open(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)));
        [exact I|exact I|exact INITIAL|exact EFFECT].
  - eapply capability_effect_preserves_private;[exact H2|apply external_capability_no_export;exact H1|
      exact INITIAL|exact H0].
  - eapply capability_effect_preserves_private with
      (action:=capability_local(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner)));
      [exact I|exact I|exact INITIAL|exact H0].
  - eapply capability_effect_preserves_private with
      (action:=capability_local(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)));
      [exact I|exact I|exact INITIAL|exact H0].
Qed.

Inductive CapabilityHistory operation groups runs native metadata external can_acquire owner child:
    CapabilityWorld->list LeanCage_Entry_CallerPhysical_Tick->CapabilityWorld->Prop:=
| capability_history_done:forall world,
    CapabilityHistory operation groups runs native metadata external can_acquire owner child world[]world
| capability_history_next:forall before tick middle ticks after,
    CapabilityObserved tick before ->
    RecordedCapabilityStep operation groups runs native metadata external can_acquire owner child before tick middle ->
    CapabilityHistory operation groups runs native metadata external can_acquire owner child middle ticks after ->
    CapabilityHistory operation groups runs native metadata external can_acquire owner child before(tick::ticks)after.

Theorem capability_history_foreign_absence operation groups runs native metadata external can_acquire owner child
    channel before ticks after offset tick actor:
  NativeCapabilityContract native can_acquire owner child ->MetadataCapabilityContract metadata can_acquire owner child ->
  capability_private_invariant(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))channel before ->
  CapabilityHistory operation groups runs native metadata external can_acquire owner child before ticks after ->
  nth_error ticks offset=Some tick ->
  unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))actor ->
  channel_absent(physical_tick_table tick actor)channel.
Proof.
  intros NATIVE METADATA INITIAL RUN;revert offset;induction RUN;intros[|offset]SELECTED OTHER;try discriminate.
  - inversion SELECTED;subst.
    intros fd binding side PRESENT OBJECT;rewrite <-H in PRESENT.
    exact((proj1 INITIAL)actor OTHER fd binding side PRESENT OBJECT).
  - eapply IHRUN;[|exact SELECTED|exact OTHER].
    eapply recorded_capability_preserves_private;eassumption.
Qed.
