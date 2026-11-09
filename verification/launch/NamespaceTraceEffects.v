(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Descriptor observations in certificates belong to the same actual source run. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber Deterministic LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceEffects NamespaceRegion
  NamespaceLibrary NamespaceStructure NamespaceTraceRegion.
Import ListNotations.
Open Scope nat_scope.

Theorem namespace_trace_duplicate ge cell R log remaining descriptor minimum k before :
  entry_errno_ready cell before ->
  (forall returned after, entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_trace_region ge cell R remaining (log++[namespace_duplicated descriptor minimum returned])
      (Returnstate (Vint returned) k after)) ->
  namespace_trace_region ge cell R (S remaining) log
    (Callstate namespace_duplicate_definition [Vint descriptor;Vint minimum] k before).
Proof.
  intros ERRNO RETURN; eapply namespace_trace_next.
  - exists (namespace_duplicated descriptor minimum Int.mone),(Returnstate (Vint Int.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_duplicate_step; [apply namespace_errno_partial_refl|exact ERRNO].
  - intros event target STEP; destruct (namespace_duplicate_cases _ _ _ _ _ _ _ _ STEP)
      as [[returned [after [FRAME [READY [EVENT TARGET]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vint returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; assumption].
    + left; auto.
    + right; left; eauto.
    + right; left; eauto.
Qed.

Theorem namespace_trace_mask ge cell R log remaining mask k before :
  entry_errno_ready cell before ->
  (forall returned after, entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_trace_region ge cell R remaining (log++[namespace_masked mask returned])
      (Returnstate (Vlong returned) k after)) ->
  namespace_trace_region ge cell R (S remaining) log (Callstate namespace_mask_definition [Vlong mask] k before).
Proof.
  intros ERRNO RETURN; eapply namespace_trace_next.
  - exists (namespace_masked mask Int64.mone),(Returnstate (Vlong Int64.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_mask_step; [apply namespace_errno_partial_refl|exact ERRNO].
  - intros event target STEP; destruct (namespace_mask_cases _ _ _ _ _ _ _ STEP)
      as [[returned [after [FRAME [READY [EVENT TARGET]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vlong returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; assumption].
    + left; auto.
    + right; left; eauto.
    + right; left; eauto.
Qed.

Theorem namespace_trace_default ge cell R log remaining signal k before :
  entry_errno_ready cell before ->
  (forall returned after, entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_trace_region ge cell R remaining (log++[namespace_defaulted signal returned])
      (Returnstate (Vlong returned) k after)) ->
  namespace_trace_region ge cell R (S remaining) log (Callstate namespace_default_definition [Vint signal] k before).
Proof.
  intros ERRNO RETURN; eapply namespace_trace_next.
  - exists (namespace_defaulted signal Int64.mone),(Returnstate (Vlong Int64.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_default_step; [apply namespace_errno_partial_refl|exact ERRNO].
  - intros event target STEP; destruct (namespace_default_cases _ _ _ _ _ _ _ STEP)
      as [[returned [after [FRAME [READY [EVENT TARGET]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vlong returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; assumption].
    + left; auto.
    + right; left; eauto.
    + right; left; eauto.
Qed.


Theorem namespace_trace_fork ge cell R log remaining k before :
  entry_errno_ready cell before ->
  (forall returned after, entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_trace_region ge cell R remaining (log++[namespace_forked returned]) (Returnstate (Vint returned) k after)) ->
  namespace_trace_region ge cell R (S remaining) log (Callstate namespace_fork_definition [] k before).
Proof.
  intros ERRNO RETURN; eapply namespace_trace_next.
  - exists (namespace_forked Int.mone),(Returnstate (Vint Int.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_fork_step; [apply namespace_errno_partial_refl|exact ERRNO].
  - intros event target STEP; destruct (namespace_fork_cases _ _ _ _ _ _ STEP)
      as [[returned [after [FRAME [READY [EVENT TARGET]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vint returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; assumption].
    + left; auto.
    + right; left; eauto.
    + right; left; eauto.
Qed.

Theorem namespace_trace_pair ge cell R log remaining domain kind protocol output offset k before :
  namespace_pair_owned before output offset -> entry_errno_ready cell before ->
  (forall returned first second after,
    namespace_pair_effect cell output offset before returned first second after -> entry_errno_ready cell after ->
    namespace_trace_region ge cell R remaining
      (log++[namespace_paired domain kind protocol output offset returned first second])
      (Returnstate (Vint returned) k after)) ->
  namespace_trace_region ge cell R (S remaining) log
    (Callstate namespace_pair_definition [Vint domain;Vint kind;Vint protocol;Vptr output offset] k before).
Proof.
  intros OWN ERRNO RETURN; eapply namespace_trace_next.
  - exists (namespace_paired domain kind protocol output offset Int.mone Int.zero Int.zero),
      (Returnstate (Vint Int.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_pair_step; [exact OWN| |exact ERRNO].
    apply namespace_pair_failed; [discriminate|apply namespace_errno_partial_refl].
  - intros event target STEP; destruct (namespace_pair_cases _ _ _ _ _ _ _ _ _ _ _ STEP)
      as [[returned [first [second [after [OWNED [FRAME [READY [EVENT TARGET]]]]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vint returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|eapply RETURN; eassumption].
    + left; auto.
    + right; left; eauto.
    + right; left; eauto.
Qed.

Theorem namespace_trace_close ge cell R log remaining fd k before :
  tls_ready cell before ->
  (forall reply after, close_effect cell before reply after ->
    namespace_trace_region ge cell R remaining
      (log++[namespace_process (process_entry (entry_library (close_returned fd reply)))])
      (Returnstate (Vint (close_value reply)) k after)) ->
  namespace_trace_region ge cell R (S remaining) log (Callstate close_definition [Vint fd] k before).
Proof.
  intros TLS RETURN; eapply namespace_trace_next.
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
    + right; left; eauto.
Qed.

Theorem namespace_trace_routine ge cell R log start schedule last remaining :
  execution ge cell start schedule last -> namespace_trace_region ge cell R remaining log last ->
  namespace_trace_region ge cell R (length schedule+remaining) log start.
Proof.
  intro SCRIPT; induction SCRIPT; intro CERT; cbn; auto.
  pose proof H as [ORDINARY [REAL [MEMORY CASES]]].
  assert (WAIT : namespace_event_waiting
    (namespace_process (process_entry (entry_library (original_event ev)))) = false).
  { destruct ORDINARY as [SOURCE|ERRNO]; subst ev; reflexivity. }
  assert (ADVANCE : namespace_advance log
    (namespace_process (process_entry (entry_library (original_event ev)))) = log).
  { destruct ORDINARY as [SOURCE|ERRNO]; subst ev; reflexivity. }
  eapply namespace_trace_next.
  - exists (namespace_process (process_entry (entry_library (original_event ev)))),next.
    split; [exact WAIT|]. split; [reflexivity|].
    apply namespace_process_step,process_entry_step,entry_library_step,original_step; exact REAL.
  - intros event target STEP.
    destruct (namespace_certain_boundary _ _ _ _ _ _ _ H STEP) as [[EVENT TARGET]|[EVENT TARGET]]; subst.
    + right; right; exists next; split; [reflexivity|]. split; [exact WAIT|]. split; [reflexivity|].
      rewrite ADVANCE; apply IHSCRIPT; exact CERT.
    + right; left; exists (memory_of s); auto.
Qed.

Theorem namespace_trace_error cell m error suffix R log remaining :
  initialized_errno cell m error -> is_call_cont suffix ->
  namespace_trace_region namespace_ge cell R remaining log (Returnstate (Vint (normalize error)) suffix m) ->
  namespace_trace_region namespace_ge cell R (source_length error+remaining)
    log (Callstate (Internal EntrySource.f_error_number) [] suffix m).
Proof.
  intros ERRNO CALL NEXT.
  assert (CONT : call_cont suffix = suffix)
    by (destruct suffix; cbn in *; try contradiction; reflexivity).
  destruct (source_execution _ _ _ _ suffix namespace_current_errno_symbols ERRNO)
    as [schedule [SCRIPT [LENGTH QUERIES]]].
  rewrite CONT in SCRIPT; rewrite <- LENGTH; eapply namespace_trace_routine; eassumption.
Qed.
