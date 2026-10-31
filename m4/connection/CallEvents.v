(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.continuation: Preserve observable event restrictions through actual calls. *)
From Coq Require Import List.
From compcert Require Import AST Integers Values Memory Events Clight.
Require Import Machine StoreSteps Library LibraryMachine LibraryPreservation LibraryControl
  CallContexts Fault.
Import ListNotations.

Definition event_contract ge cell start (allowed : library_event -> Prop) :=
  forall events target, library_steps ge cell (live start) events target -> Forall allowed events.

Theorem source_path_event_contract : forall ge cell P start count last allowed,
  store_path ge P start count last ->
  allowed (original_event (source_step E0)) -> allowed (original_event loss_step) ->
  event_contract ge cell last allowed -> event_contract ge cell start allowed.
Proof.
  intros ge cell P start count last allowed PATH SOURCE LOSS LAST; induction PATH;
    [exact LAST|]. intros events target RUN; inversion RUN; subst; [constructor|].
  destruct H0 as [IN [REAL UNIQUE]].
  match goal with STEP : library_step _ _ _ _ _ |- _ =>
    destruct (internal_boundary_unchanged _ _ _ _ _ IN STEP) as [old [EV OLD]] end; subst.
  destruct (store_edge_cases _ _ _ _ _ _ (conj IN (conj REAL UNIQUE)) OLD) as [[EV TARGET]|[EV TARGET]]; subst.
  - constructor; [exact SOURCE|eapply (IHPATH LAST _ _); eassumption].
  - match goal with TAIL : library_steps _ _ (dead _) _ _ |- _ =>
      destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES EQ] end; subst.
    constructor; [exact LOSS|constructor].
Qed.

Lemma return_event_contract : forall ge cell value m allowed,
  allowed (original_event loss_step) -> event_contract ge cell (Returnstate value Kstop m) allowed.
Proof.
  intros ge cell value m allowed LOSS events target RUN; inversion RUN; subst; [constructor|].
  match goal with STEP : library_step _ _ _ _ _ |- _ =>
    destruct (control_return_step _ _ _ _ _ _ STEP) as [EV TARGET] end; subst.
  match goal with TAIL : library_steps _ _ (dead _) _ _ |- _ =>
    destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES EQ] end; subst.
  constructor; [exact LOSS|constructor].
Qed.

Theorem strcmp_event_contract : forall ge cell m left right xs ys k allowed,
  c_string m left xs -> c_string m right ys ->
  allowed library_wait -> allowed (original_event loss_step) ->
  (forall value, strcmp_result m left right value -> allowed (strcmp_returned left right value)) ->
  (forall value, strcmp_result m left right value ->
    event_contract ge cell (Returnstate (Vint value) k m) allowed) ->
  event_contract ge cell (Callstate strcmp_definition [address_value left;address_value right] k m) allowed.
Proof.
  intros ge cell m left right xs ys k allowed LEFT RIGHT WAIT LOSS COMPARE RETURN events.
  induction events as [|ev events IH]; intros target RUN; inversion RUN; subst; [constructor|].
  match goal with STEP : library_step _ _ _ _ _ |- _ =>
    destruct (strcmp_boundary_cases _ _ _ _ _ _ _ _ _ _ LEFT RIGHT STEP)
      as [[value [RESULT [EV TARGET]]]|[[EV TARGET]|[EV TARGET]]] end; subst.
  - constructor; [apply COMPARE; exact RESULT|eapply (RETURN value RESULT _ _); eassumption].
  - constructor; [exact WAIT|eapply IH; eassumption].
  - match goal with TAIL : library_steps _ _ (dead _) _ _ |- _ =>
      destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES EQ] end; subst.
    constructor; [exact LOSS|constructor].
Qed.

Definition selector_event ev := match ev with
  | original_event (source_step _) | original_event loss_step | library_wait
  | strcmp_returned _ _ _ => True | _ => False end.

Theorem fault_events_are_selectors : forall ge cell m mode name xs ys,
  fault_symbols ge -> fault_input ge m mode name xs ys ->
  event_contract ge cell (fault_initial name Kstop m) selector_event.
Proof.
  intros ge cell m mode name xs ys SYMBOLS [MODE [LEFT RIGHT]].
  eapply source_path_event_contract with (count:=6%nat).
  - exact (fault_to_comparison ge m mode name Kstop SYMBOLS MODE).
  - exact I.
  - exact I.
  - eapply strcmp_event_contract; [exact LEFT|exact RIGHT|exact I|exact I|intros; exact I|].
    intros value RESULT. eapply source_path_event_contract with (count:=3%nat).
    + apply fault_after_comparison.
    + exact I.
    + exact I.
    + apply return_event_contract; exact I.
Qed.

Theorem call_event_contract : forall ge cell start suffix allowed,
  is_call_cont suffix -> event_contract ge cell start allowed ->
  (forall events value m,
    library_steps ge cell (live start) events (live (Returnstate value Kstop m)) ->
    event_contract ge cell (Returnstate value suffix m) allowed) ->
  event_contract ge cell (plug_state start suffix) allowed.
Proof.
  intros ge cell start suffix allowed CALL LOCAL RETURN events target RUN.
  destruct (caller_run_decomposition _ _ _ _ _ _ CALL RUN)
    as [[last [PREFIX SAME]]|[before [after [value [m [ES [PREFIX TAIL]]]]]]].
  - exact (LOCAL _ _ PREFIX).
  - subst events. apply Forall_app; split; [exact (LOCAL _ _ PREFIX)|exact (RETURN before value m PREFIX after target TAIL)].
Qed.
