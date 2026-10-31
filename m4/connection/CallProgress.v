(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.continuation: Ordinary enabled progress under actual caller composition. *)
From Coq Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps LibraryMachine LibraryPreservation LibraryControl CallContexts CallPaths.
Import ListNotations.

Definition live_progress ge cell start := forall events s,
  library_steps ge cell (live start) events (live s) ->
  exists ev target, control_progress ev /\ library_step ge cell (live s) ev target.
Definition procedure_progress ge cell start (R : val -> mem -> Prop) := forall events s,
  library_steps ge cell (live start) events (live s) ->
  (exists value m, s = Returnstate value Kstop m /\ R value m) \/
  (exists ev target, control_progress ev /\ library_step ge cell (live s) ev target).

Lemma return_no_progress : forall ge cell value m ev target,
  library_step ge cell (live (Returnstate value Kstop m)) ev target -> ~ control_progress ev.
Proof.
  intros ge cell value m ev target STEP [_ [NOTLOSS _]].
  destruct (control_return_step _ _ _ _ _ _ STEP) as [EQ _]; contradiction.
Qed.

Lemma procedure_return_post : forall ge cell start R events value m,
  procedure_progress ge cell start R ->
  library_steps ge cell (live start) events (live (Returnstate value Kstop m)) -> R value m.
Proof.
  intros ge cell start R events value m PROC RUN.
  destruct (PROC _ _ RUN) as [[v [after [EQ POST]]]|[ev [target [ADV STEP]]]].
  - inversion EQ; subst; exact POST.
  - exfalso; eapply return_no_progress; eassumption.
Qed.

Theorem call_live_progress : forall ge cell start suffix R,
  is_call_cont suffix -> procedure_progress ge cell start R ->
  (forall value m, R value m -> live_progress ge cell (Returnstate value suffix m)) ->
  live_progress ge cell (plug_state start suffix).
Proof.
  intros ge cell start suffix R CALL PROC RETURN events current RUN.
  destruct (caller_run_decomposition _ _ _ _ _ _ CALL RUN)
    as [[local [LOCAL SAME]]|[before [after [value [m [ES [LOCAL TAIL]]]]]]].
  - destruct local as [s|m]; cbn in SAME; [inversion SAME; subst current|discriminate].
    destruct (PROC _ _ LOCAL) as [[value [m [EQ POST]]]|[ev [target [ADV STEP]]]].
    + subst s; apply (RETURN value m POST []); constructor.
    + exists ev, (plug_machine target suffix); split; [exact ADV|].
      exact (plug_library_step _ _ _ _ _ _ CALL STEP).
  - apply (RETURN value m (procedure_return_post _ _ _ _ _ _ _ PROC LOCAL) after current TAIL).
Qed.

Theorem source_path_live_progress : forall ge cell P start count last,
  store_path ge P start count last -> live_progress ge cell last -> live_progress ge cell start.
Proof.
  intros ge cell P start count last PATH LAST events current RUN.
  destruct (source_path_caller_prefix _ _ _ _ _ _ PATH _ _ RUN)
    as [[n [s [remaining [_ [_ [SAME TAIL]]]]]]|[[n [m [_ [_ [SAME _]]]]]|[rest [_ AFTER]]]].
  - inversion SAME; subst s. inversion TAIL; subst.
    + apply (LAST []); constructor.
    + exists (original_event (source_step E0)), (live next). split.
      * unfold control_progress; cbn; repeat split; discriminate.
      * constructor. match goal with EDGE : store_edge _ _ _ |- _ => destruct EDGE as [IN [REAL _]] end.
        apply internal; assumption.
  - discriminate.
  - exact (LAST _ _ AFTER).
Qed.

Theorem live_progress_never_returns : forall ge cell start,
  live_progress ge cell start -> forall events value m,
  ~ library_steps ge cell (live start) events (live (Returnstate value Kstop m)).
Proof.
  intros ge cell start PROGRESS events value m RUN.
  destruct (PROGRESS _ _ RUN) as [ev [target [ADV STEP]]].
  eapply return_no_progress; eassumption.
Qed.
