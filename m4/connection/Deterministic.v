(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.errno: Finite real source paths with deterministic errno effects. *)
From Coq Require Import List Lia.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine ClightSteps.
Import ListNotations.

Definition routine_event (ev : event) := ev = source_step E0 \/ ev = errno_step.

(* This certificate proves existence AND classifies all steps of the unchanged
   machine. Loss remains possible at every boundary; no transition is removed. *)
Definition certain_step ge cell s ev next : Prop :=
  routine_event ev /\ step ge cell (live s) ev (live next) /\
  memory_of next = memory_of s /\
  (forall event target, step ge cell (live s) event target ->
    (event = ev /\ target = live next) \/
    (event = loss_step /\ target = dead (memory_of s))).

Inductive execution ge cell : Clight.state -> list event -> Clight.state -> Prop :=
| execution_done : forall s, execution ge cell s [] s
| execution_next : forall s ev next events last,
    certain_step ge cell s ev next -> execution ge cell next events last ->
    execution ge cell s (ev :: events) last.

Lemma internal_certain : forall ge cell s next,
  edge ge s next -> certain_step ge cell s (source_step E0) next.
Proof.
  intros ge cell s next EDGE. split; [left; reflexivity|].
  pose proof EDGE as [IN [REAL [MEM UNIQUE]]]. split.
  - apply internal; assumption.
  - split; [assumption|]. intros; eapply machine_edge_cases; eauto.
Qed.

Lemma execution_memory : forall ge cell s events last,
  execution ge cell s events last -> memory_of last = memory_of s.
Proof.
  intros ge cell s events last RUN; induction RUN; auto.
  destruct H as [_ [_ [MEM _]]]; congruence.
Qed.

Lemma execution_actual : forall ge cell s events last,
  execution ge cell s events last -> steps ge cell (live s) events (live last).
Proof.
  intros ge cell s events last RUN; induction RUN; [constructor|].
  destruct H as [_ [REAL _]]. econstructor; eassumption.
Qed.

Lemma execution_ordinary : forall ge cell s events last,
  execution ge cell s events last -> Forall routine_event events.
Proof.
  intros ge cell s events last RUN; induction RUN; constructor; auto.
  destruct H as [ORD _]; assumption.
Qed.

Lemma execution_trans : forall ge cell a first b second c,
  execution ge cell a first b -> execution ge cell b second c ->
  execution ge cell a (first ++ second) c.
Proof. intros ge cell a first b second c AB BC; induction AB; simpl; eauto using execution_next. Qed.

Lemma dead_steps : forall ge cell m events target,
  steps ge cell (dead m) events target -> events = [] /\ target = dead m.
Proof. intros ge cell m events target RUN; inversion RUN; subst; auto. inversion H. Qed.

Lemma returned_step : forall ge cell value m ev target,
  step ge cell (live (Returnstate value Kstop m)) ev target ->
  ev = loss_step /\ target = dead m.
Proof.
  intros ge cell value m ev target STEP; inversion STEP; subst; auto;
    try match goal with H : boundary _ _ _ |- _ => inversion H end.
  match goal with H : step2 _ _ _ _ |- _ => inversion H end.
Qed.

(* Every execution is a prefix of the checked ordinary path, or such a prefix
   followed by one loss event. This includes loss after the source return. *)
Theorem execution_classifies_all : forall ge cell start schedule value m,
  execution ge cell start schedule (Returnstate value Kstop m) ->
  forall events target, steps ge cell (live start) events target ->
  (exists rest s, target = live s /\ schedule = events ++ rest /\
    execution ge cell s rest (Returnstate value Kstop m)) \/
  (exists before after, schedule = before ++ after /\
    events = before ++ [loss_step] /\ target = dead m).
Proof.
  intros ge cell start schedule value m SCRIPT events target RUN.
  remember (live start) as initial eqn:INIT.
  revert start schedule INIT SCRIPT.
  induction RUN as [initial|initial ev mid events target STEP RUN IH];
    intros start schedule INIT SCRIPT; subst initial.
  - left. exists schedule, start. auto.
  - inversion SCRIPT as [|s event next rest last CERT TAIL]; subst.
    + destruct (returned_step _ _ _ _ _ _ STEP) as [EV TARGET]; subst.
      destruct (dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
      right. exists [], []. auto.
    + destruct CERT as [ORD [REAL [MEM UNIQUE]]].
      destruct (UNIQUE _ _ STEP) as [[EV TARGET]|[EV TARGET]]; subst.
      * destruct (IH _ _ eq_refl TAIL) as [[suffix [s [TARGET [SCHED REST]]]]|
          [before [after [SCHED [EVENTS TARGET]]]]].
        -- left. exists suffix, s. split; [assumption|]. split; [simpl; congruence|assumption].
        -- right. exists (event :: before), after. simpl. repeat split; congruence.
      * destruct (dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
        pose proof (execution_memory _ _ _ _ _ SCRIPT) as SAME. simpl in SAME.
        right. exists [], (event :: rest). simpl. repeat split; congruence.
Qed.

Lemma returned_execution : forall ge cell value m events final,
  execution ge cell (Returnstate value Kstop m) events final ->
  events = [] /\ final = Returnstate value Kstop m.
Proof.
  intros ge cell value m events final RUN; inversion RUN; subst; auto.
  destruct H as [ORD [REAL _]].
  destruct (returned_step _ _ _ _ _ _ REAL) as [EV TARGET]. discriminate.
Qed.

Theorem execution_return_exact : forall ge cell start schedule value m events actual after,
  execution ge cell start schedule (Returnstate value Kstop m) ->
  steps ge cell (live start) events (live (Returnstate actual Kstop after)) ->
  actual = value /\ after = m /\ events = schedule.
Proof.
  intros ge cell start schedule value m events actual after SCRIPT RUN.
  destruct (execution_classifies_all _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[rest [s [TARGET [SCHED TAIL]]]]|[before [rest [_ [_ TARGET]]]]];
    try discriminate.
  inversion TARGET; subst s.
  destruct (returned_execution _ _ _ _ _ _ TAIL) as [REST SAME].
  inversion SAME; subst. rewrite app_nil_r; auto.
Qed.

Theorem execution_prefix_defined : forall ge cell start schedule value m events s,
  execution ge cell start schedule (Returnstate value Kstop m) ->
  steps ge cell (live start) events (live s) ->
  s = Returnstate value Kstop m \/
    exists ev next, routine_event ev /\ step ge cell (live s) ev (live next).
Proof.
  intros ge cell start schedule value m events s SCRIPT RUN.
  destruct (execution_classifies_all _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[rest [s' [TARGET [SCHED TAIL]]]]|[before [rest [_ [_ TARGET]]]]]; try discriminate.
  inversion TARGET; subst s'. inversion TAIL; subst; auto.
  right. destruct H as [ORD [REAL _]]. eauto.
Qed.

Theorem execution_length_bound : forall ge cell start schedule value m events target,
  execution ge cell start schedule (Returnstate value Kstop m) ->
  steps ge cell (live start) events target ->
  length events <= S (length schedule).
Proof.
  intros ge cell start schedule value m events target SCRIPT RUN.
  destruct (execution_classifies_all _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[rest [s [_ [SCHED _]]]]|[before [rest [SCHED [EVENTS _]]]]];
    subst; rewrite !app_length; simpl; lia.
Qed.

Definition routine_memory (s : machine) :=
  match s with live state => memory_of state | dead m => m end.
Definition allowed_event ev := routine_event ev \/ ev = loss_step.

Theorem execution_preserves_memory : forall ge cell start schedule value m events target,
  execution ge cell start schedule (Returnstate value Kstop m) ->
  steps ge cell (live start) events target -> routine_memory target = m.
Proof.
  intros ge cell start schedule value m events target SCRIPT RUN.
  destruct (execution_classifies_all _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[rest [s [TARGET [_ TAIL]]]]|[before [rest [_ [_ TARGET]]]]]; subst; cbn; auto.
  symmetry. exact (execution_memory _ _ _ _ _ TAIL).
Qed.

Theorem execution_events : forall ge cell start schedule value m events target,
  execution ge cell start schedule (Returnstate value Kstop m) ->
  steps ge cell (live start) events target -> Forall allowed_event events.
Proof.
  intros ge cell start schedule value m events target SCRIPT RUN.
  pose proof (execution_ordinary _ _ _ _ _ SCRIPT) as ALL.
  destruct (execution_classifies_all _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[rest [s [_ [SCHED _]]]]|[before [rest [SCHED [EVENTS _]]]]]; subst;
    rewrite Forall_app in ALL; destruct ALL as [PREFIX _].
  - eapply Forall_impl; [|exact PREFIX]. intros; left; assumption.
  - apply Forall_app. split.
    + eapply Forall_impl; [|exact PREFIX]. intros; left; assumption.
    + constructor; [right; reflexivity|constructor].
Qed.

Lemma execution_split : forall ge cell start events last,
  execution ge cell start events last ->
  forall before after, events = before ++ after ->
  exists mid, execution ge cell start before mid /\ execution ge cell mid after last.
Proof.
  intros ge cell start events last SCRIPT; induction SCRIPT;
    intros before after EQ; destruct before; cbn in EQ.
  - subst; exists s; split; constructor.
  - discriminate.
  - subst; exists s; split; [constructor|econstructor; eassumption].
  - inversion EQ; subst. destruct (IHSCRIPT _ _ eq_refl) as [mid [A B]].
    exists mid; split; [econstructor; eassumption|assumption].
Qed.

Theorem execution_loss_every_prefix : forall ge cell start schedule final n,
  execution ge cell start schedule final ->
  exists mid, steps ge cell (live start) (firstn n schedule) (live mid) /\
    steps ge cell (live start) (firstn n schedule ++ [loss_step]) (dead (memory_of final)).
Proof.
  intros ge cell start schedule final n SCRIPT.
  destruct (execution_split _ _ _ _ _ SCRIPT (firstn n schedule) (skipn n schedule)
    (eq_sym (firstn_skipn n schedule))) as [mid [BEFORE AFTER]].
  exists mid; split; [apply execution_actual; assumption|].
  pose proof (execution_memory _ _ _ _ _ AFTER) as SAME. rewrite SAME.
  clear AFTER SAME SCRIPT. induction BEFORE; cbn.
  - econstructor; [constructor|constructor].
  - destruct H as [_ [STEP _]]. econstructor; eassumption.
Qed.
