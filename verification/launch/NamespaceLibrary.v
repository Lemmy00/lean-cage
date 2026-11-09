(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Reuse checked errno normalization and exact close effects in local failures. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Slice IO Machine ErrorNumber Deterministic WriteAll StoreSteps LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceRegion.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_errno_original ge cell k m event target :
  namespace_step ge cell
    (live (Callstate (External errno_function [] (tptr tint) cc_default) [] k m)) event target ->
  exists original,
    event = namespace_process (process_entry (entry_library (original_event original))) /\
    Machine.step ge cell
      (live (Callstate (External errno_function [] (tptr tint) cc_default) [] k m)) original target.
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  - inversion H; subst; try discriminate.
    inversion H0; subst; try discriminate.
    match goal with BASE : library_step _ _ _ _ _ |- _ => inversion BASE; subst; try discriminate end.
    + eexists; split; [reflexivity|eassumption].
    + match goal with READY : library_ready _ _ |- _ => inversion READY end.
  - match goal with READY : namespace_ready _ |- _ => inversion READY end.
Qed.

Lemma namespace_certain_boundary ge cell state original next event target :
  certain_step ge cell state original next -> namespace_step ge cell (live state) event target ->
  (event = namespace_process (process_entry (entry_library (original_event original))) /\ target = live next) \/
  (event = namespace_process (process_entry (entry_library (original_event loss_step))) /\
    target = dead (memory_of state)).
Proof.
  intros [ORDINARY [REAL [MEMORY CASES]]] STEP.
  assert (ORIGINAL : exists old,
    event = namespace_process (process_entry (entry_library (original_event old))) /\
    Machine.step ge cell (live state) old target).
  { destruct ORDINARY as [SOURCE|ERRNO]; subst original.
    - assert (INTERNAL : internal_state state) by (inversion REAL; subst; assumption).
      exact (namespace_internal_step_exact _ _ _ _ _ INTERNAL STEP).
    - inversion REAL; subst; try discriminate.
      exact (namespace_errno_original _ _ _ _ _ _ STEP). }
  destruct ORIGINAL as [old [EVENT BASE]]; subst event.
  destruct (CASES _ _ BASE) as [[EVENT TARGET]|[EVENT TARGET]]; subst; auto.
Qed.

Theorem namespace_region_execution ge cell P R start schedule last remaining :
  execution ge cell start schedule last -> P (memory_of start) ->
  namespace_region ge cell P R remaining last ->
  namespace_region ge cell P R (length schedule+remaining)%nat start.
Proof.
  intro SCRIPT; induction SCRIPT; intros GOOD CERT; cbn; auto.
  pose proof H as [ORDINARY [REAL [MEMORY CASES]]].
  assert (WAIT : namespace_event_waiting
    (namespace_process (process_entry (entry_library (original_event ev)))) = false).
  { destruct ORDINARY as [SOURCE|ERRNO]; subst ev; reflexivity. }
  eapply namespace_region_next; [exact GOOD| |].
  - exists (namespace_process (process_entry (entry_library (original_event ev)))),next.
    split; [exact WAIT|]. split; [reflexivity|].
    apply namespace_process_step,process_entry_step,entry_library_step,original_step; exact REAL.
  - intros event target STEP.
    destruct (namespace_certain_boundary _ _ _ _ _ _ _ H STEP) as [[EVENT TARGET]|[EVENT TARGET]]; subst.
    + right; right; exists next; split; [reflexivity|]. split; [exact WAIT|].
      split; [reflexivity|apply IHSCRIPT; [rewrite MEMORY; exact GOOD|exact CERT]].
    + right; left; exists (memory_of s); auto.
Qed.

Lemma namespace_current_errno_symbols : WriteAll.symbols namespace_ge.
Proof. split; eexists; split; vm_compute; reflexivity. Qed.

Theorem namespace_current_error_region cell m error suffix P R remaining :
  initialized_errno cell m error -> is_call_cont suffix -> P m ->
  namespace_region namespace_ge cell P R remaining (Returnstate (Vint (normalize error)) suffix m) ->
  namespace_region namespace_ge cell P R (source_length error+remaining)%nat
    (Callstate (Internal EntrySource.f_error_number) [] suffix m).
Proof.
  intros ERRNO CALL GOOD NEXT.
  assert (CONT : call_cont suffix = suffix)
    by (destruct suffix; cbn in *; try contradiction; reflexivity).
  destruct (source_execution _ _ _ _ suffix namespace_current_errno_symbols ERRNO)
    as [schedule [SCRIPT [LENGTH QUERIES]]].
  rewrite CONT in SCRIPT; rewrite <- LENGTH.
  eapply namespace_region_execution; [exact SCRIPT|exact GOOD|exact NEXT].
Qed.

Lemma namespace_close_library ge cell fd k before event target :
  namespace_step ge cell (live (Callstate close_definition [Vint fd] k before)) event target ->
  exists original, event = namespace_process (process_entry (entry_library original)) /\
    library_step ge cell (live (Callstate close_definition [Vint fd] k before)) original target.
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  - inversion H; subst; try discriminate.
    inversion H0; subst; try discriminate; eauto.
  - match goal with READY : namespace_ready _ |- _ => inversion READY end.
Qed.

Theorem namespace_close_cases ge cell fd k before event target :
  namespace_step ge cell (live (Callstate close_definition [Vint fd] k before)) event target ->
  (exists reply after, close_effect cell before reply after /\
    event = namespace_process (process_entry (entry_library (close_returned fd reply))) /\
    target = live (Returnstate (Vint (close_value reply)) k after)) \/
  (event = namespace_process (process_entry (entry_library library_wait)) /\
    target = live (Callstate close_definition [Vint fd] k before)) \/
  (event = namespace_process (process_entry (entry_library (original_event loss_step))) /\ target = dead before).
Proof.
  intro STEP; destruct (namespace_close_library _ _ _ _ _ _ _ STEP) as [old [EVENT BASE]]; subst event.
  inversion BASE; subst; try discriminate.
  - inversion H; subst; cbn in *; try contradiction; auto;
      match goal with BOUNDARY : boundary _ _ _ |- _ =>
        inversion BOUNDARY; subst; destruct (operation q); discriminate end.
  - left; do 2 eexists; split; [eassumption|]; split; reflexivity.
  - right; left; auto.
Qed.

Theorem namespace_close_region ge cell P R remaining fd k before :
  P before -> tls_ready cell before ->
  (forall reply after, close_effect cell before reply after ->
    namespace_region ge cell P R remaining (Returnstate (Vint (close_value reply)) k after)) ->
  namespace_region ge cell P R (S remaining) (Callstate close_definition [Vint fd] k before).
Proof.
  intros GOOD TLS RETURN; eapply namespace_region_next; [exact GOOD| |].
  - exists (namespace_process (process_entry (entry_library (close_returned fd (close_ok None))))),
      (Returnstate (Vint Int.zero) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_process_step,process_entry_step,entry_library_step,close_step.
    split; [exact TLS|constructor].
  - intros event target STEP; destruct (namespace_close_cases _ _ _ _ _ _ _ STEP)
      as [[reply [after [CLOSE [EVENT TARGET]]]]|[[EVENT TARGET]|[EVENT TARGET]]]; subst.
    + right; right; exists (Returnstate (Vint (close_value reply)) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; exact CLOSE].
    + left; auto.
    + right; left; exists before; auto.
Qed.
