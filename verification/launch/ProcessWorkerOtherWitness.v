(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Advance the useful owned worker one actual operation at a time. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds ProcessLaunchWitness ProcessLaunchRecordingWitness
  ProcessParentRecordingWitness ProcessRecordedComposition ProcessChildOtherWitness.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceWorldTrace NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.

Lemma launch_worker_effect_interference before code after:
  LaunchChildEffect before code after ->ProcessInterference physical_parent physical_child before after.
Proof.
  intro EFFECT;destruct EFFECT;try apply source_interference_refl.
  all:apply process_interference_frame;try reflexivity;intro EXITED;discriminate.
Qed.

(* The label is the actual request kind/code/origin recorded by the ordinary
   native or metadata return adapter. No label map may choose another equal Tick. *)
Inductive UsefulWorkerOther:ProcessWorld->LeanCage_Entry_CallerPhysical_Tick->ProcessWorld->Prop:=
| useful_worker_native:forall before tick code after,
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference ->
    LeanCage_Entry_CallerPhysical_Tick_primitive tick=
      ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_PrimitiveLabel
        (LeanCage_Entry_CallerPhysical_PrimitiveLabel_mk LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
          (Nat_of_nat code)ProcessImport.Bool_true) ->
    SourceProcessView before physical_child(LeanCage_Entry_CallerPhysical_Tick_before tick) ->
    SourceProcessView after physical_child(LeanCage_Entry_CallerPhysical_Tick_after tick) ->
    LaunchChildEffect before code after ->UsefulWorkerOther before tick after
| useful_worker_metadata:forall world tick code,
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference ->
    LeanCage_Entry_CallerPhysical_Tick_primitive tick=
      ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_PrimitiveLabel
        (LeanCage_Entry_CallerPhysical_PrimitiveLabel_mk LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata
          (Nat_of_nat code)ProcessImport.Bool_true) ->
    (code=0%nat\/code=1%nat\/code=2%nat) ->
    SourceProcessView world physical_child(LeanCage_Entry_CallerPhysical_Tick_before tick) ->
    SourceProcessView world physical_child(LeanCage_Entry_CallerPhysical_Tick_after tick) ->
    UsefulWorkerOther world tick world.

Theorem useful_worker_other_contract groups:
  SourceOtherContract UsefulWorkerOther groups physical_parent physical_child.
Proof.
  constructor;intros before tick after OWN OTHER WRITES LIVE;destruct OTHER.
  - eapply launch_worker_effect_interference;exact H3.
  - apply source_interference_refl.
Qed.

Inductive UsefulEntryOther groups runs:ProcessWorld->LeanCage_Entry_CallerPhysical_Tick->ProcessWorld->Prop:=
| useful_entry_child:forall before tick after,UsefulChildOther groups runs before tick after ->UsefulEntryOther groups runs before tick after
| useful_entry_worker:forall before tick after,UsefulWorkerOther before tick after ->UsefulEntryOther groups runs before tick after.

Theorem useful_entry_other_contract groups runs:
  SourceOtherContract(UsefulEntryOther groups runs)groups physical_parent physical_child.
Proof.
  constructor;intros before tick after OWN OTHER WRITES LIVE;destruct OTHER.
  - exact(source_other_interference _ _ _ _(useful_child_other_contract groups runs)_ _ _ OWN H WRITES LIVE).
  - exact(source_other_interference _ _ _ _(useful_worker_other_contract groups)_ _ _ OWN H WRITES LIVE).
Qed.

Inductive UsefulWorkerRun:ProcessWorld->list LeanCage_Entry_CallerPhysical_Tick->ProcessWorld->Prop:=
| useful_worker_done:forall world,UsefulWorkerRun world[]world
| useful_worker_next:forall before tick middle ticks after,
    UsefulWorkerOther before tick middle ->UsefulWorkerRun middle ticks after ->UsefulWorkerRun before(tick::ticks)after.

Lemma useful_worker_source_none before tick after:
  UsefulWorkerOther before tick after ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=
    ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference.
Proof. intro STEP;destruct STEP;assumption. Qed.

Theorem useful_worker_process_schedule groups runs tracked cursor worlds before ticks after:
  UsefulWorkerRun before ticks after ->
  SourceProcessSchedule launch_operation groups launch_recording_child runs tracked(UsefulEntryOther groups runs)
    cursor worlds before ticks cursor worlds after.
Proof.
  intro RUN;induction RUN;[constructor|].
  eapply source_process_cons;[|exact IHRUN].
  eapply source_process_other with(middle:=cursor)(middle_worlds:=worlds).
  - apply source_table_external;eapply useful_worker_source_none;exact H.
  - intro ordinal;rewrite(useful_worker_source_none _ _ _ H);discriminate.
  - constructor;exact H.
Qed.

Theorem useful_worker_run_append before first middle last after:
  UsefulWorkerRun before first middle ->UsefulWorkerRun middle last after ->UsefulWorkerRun before(first++last)after.
Proof. intro FIRST;induction FIRST;intro LAST;[exact LAST|cbn;econstructor;eauto]. Qed.
