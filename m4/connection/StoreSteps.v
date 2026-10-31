(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.writers: Actual source stores, including every loss boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps Deterministic.
Import ListNotations.

Definition store_edge ge s next : Prop :=
  internal_state s /\ step2 ge s E0 next /\
  (forall t other, step2 ge s t other -> t = E0 /\ other = next).

Lemma unchanged_store_edge : forall ge s next,
  edge ge s next -> store_edge ge s next.
Proof. intros ge s next [A [B [C D]]]; unfold store_edge; auto. Qed.

Lemma byte_assignment : forall ge f p a k e le m b ofs value after,
  evaluated ge e le m p (Vptr b ofs) ->
  evaluated ge e le m a (Vint value) ->
  sem_cast (Vint value) (typeof a) tuchar m = Some (Vint value) ->
  Mem.storev Mint8unsigned m (Vptr b ofs) (Vint value) = Some after ->
  store_edge ge (State f (Sassign (Ederef p tuchar) a) k e le m)
    (State f Sskip k e le after).
Proof.
  intros ge f p a k e le m b ofs value after PTR VAL CAST STORE.
  split; [exact I|]. split.
  - eapply step_assign; [eapply eval_Ederef; eapply evaluated_sound; exact PTR|
      eapply evaluated_sound; exact VAL|exact CAST|].
    eapply assign_loc_value; [reflexivity|exact STORE].
  - intros t other STEP; inversion STEP; subst;
      try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
    match goal with H : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ => inversion H; subst end.
    match goal with H : eval_expr _ _ _ _ p _ |- _ =>
      pose proof (evaluated_unique _ _ _ _ _ _ PTR _ H) as EQ; inversion EQ; subst; clear EQ end.
    match goal with H : eval_expr _ _ _ _ a _ |- _ =>
      pose proof (evaluated_unique _ _ _ _ _ _ VAL _ H) as EQ; subst end.
    match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion H; subst; simpl in * end;
      try discriminate.
    match goal with H : By_value _ = By_value _ |- _ => inversion H; subst end.
    assert (v = Vint value) by congruence; subst v. cbn in *.
    split; [reflexivity|]. f_equal; congruence.
Qed.

Lemma void_return_edge : forall ge f k le m,
  is_call_cont k -> store_edge ge (State f Sskip k empty_env le m)
    (Returnstate Vundef k m).
Proof.
  intros ge f k le m K. split; [exact I|]. split.
  - apply step_skip_call; [assumption|reflexivity].
  - intros t other STEP; inversion STEP; subst; simpl in *; try contradiction.
    match goal with H : Some _ = Some _ |- _ => inversion H; subst end. auto.
Qed.

Lemma store_edge_cases : forall ge cell s next ev target,
  store_edge ge s next -> step ge cell (live s) ev target ->
  (ev = source_step E0 /\ target = live next) \/
  (ev = loss_step /\ target = dead (memory_of s)).
Proof.
  intros ge cell s next ev target [IN [REAL UNIQUE]] STEP.
  inversion STEP; subst; try contradiction.
  - destruct (UNIQUE _ _ H1); subst; auto.
  - match goal with B : boundary _ _ _ |- _ => inversion B; subst end. contradiction.
  - auto.
Qed.

(* P constrains each real intermediate memory; it is not an execution premise
   at the public writer interface. Writer certificates below construct it from
   independent writable-buffer ownership. *)
Inductive store_path ge (P : mem -> Prop) : Clight.state -> nat -> Clight.state -> Prop :=
| store_done : forall s, P (memory_of s) -> store_path ge P s 0 s
| store_next : forall s next n last,
    P (memory_of s) -> store_edge ge s next -> store_path ge P next n last ->
    store_path ge P s (S n) last.

Lemma store_path_initial : forall ge P s n last,
  store_path ge P s n last -> P (memory_of s).
Proof. intros; inversion H; assumption. Qed.

Lemma store_path_actual : forall ge cell P s n last,
  store_path ge P s n last ->
  steps ge cell (live s) (repeat (source_step E0) n) (live last).
Proof.
  intros ge cell P s n last RUN; induction RUN; cbn; [constructor|].
  destruct H0 as [IN [REAL _]]. econstructor; [apply internal; eassumption|assumption].
Qed.

Lemma store_path_trans : forall ge P a n b k c,
  store_path ge P a n b -> store_path ge P b k c -> store_path ge P a (n + k) c.
Proof. intros ge P a n b k c AB BC; induction AB; cbn; eauto using store_next. Qed.

(* The dead alternative retains the memory at the actual interrupted source
   state, rather than silently replacing it with the final buffer. *)
Theorem store_path_all : forall ge cell P start count value final,
  store_path ge P start count (Returnstate value Kstop final) ->
  forall events target, steps ge cell (live start) events target ->
  (exists n s rest, (count = n + rest)%nat /\
    events = repeat (source_step E0) n /\ target = live s /\
    store_path ge P s rest (Returnstate value Kstop final)) \/
  (exists n m, (n <= count)%nat /\
    events = repeat (source_step E0) n ++ [loss_step] /\ target = dead m /\ P m).
Proof.
  intros ge cell P start count value final SCRIPT events target RUN.
  remember (live start) as initial eqn:INIT. revert start count INIT SCRIPT.
  induction RUN as [initial|initial ev mid events target STEP RUN IH];
    intros start count INIT SCRIPT; subst initial.
  - left. exists 0%nat, start, count. cbn; auto.
  - inversion SCRIPT as [s GOOD|s next n last GOOD EDGE TAIL]; subst.
    + destruct (returned_step _ _ _ _ _ _ STEP) as [EV TARGET]; subst.
      destruct (dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
      right. exists 0%nat, final. cbn in *; auto.
    + destruct (store_edge_cases _ _ _ _ _ _ EDGE STEP) as [[EV TARGET]|[EV TARGET]]; subst.
      * destruct (IH _ _ eq_refl TAIL) as [[j [s [rest [COUNT [ES [TARGET REST]]]]]]|
          [j [m [COUNT [ES [TARGET GOOD']]]]]]; subst.
        -- left. exists (S j), s, rest. cbn; auto.
        -- right. exists (S j), m. cbn. repeat split; auto; lia.
      * destruct (dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
        right. exists 0%nat, (memory_of start). cbn; auto with arith.
Qed.

Lemma store_return_path : forall ge P value m count last,
  store_path ge P (Returnstate value Kstop m) count last ->
  count = 0%nat /\ last = Returnstate value Kstop m.
Proof.
  intros ge P value m count last RUN; inversion RUN; subst; auto.
  destruct H0 as [_ [REAL _]]. inversion REAL.
Qed.

Theorem store_path_return_exact : forall ge cell P start count value final events actual after,
  store_path ge P start count (Returnstate value Kstop final) ->
  steps ge cell (live start) events (live (Returnstate actual Kstop after)) ->
  actual = value /\ after = final /\ events = repeat (source_step E0) count.
Proof.
  intros ge cell P start count value final events actual after SCRIPT RUN.
  destruct (store_path_all _ _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[n [s [rest [COUNT [ES [TARGET TAIL]]]]]]|[n [m [_ [_ [TARGET _]]]]]];
    try discriminate.
  inversion TARGET; subst s.
  destruct (store_return_path _ _ _ _ _ _ TAIL) as [REST SAME].
  inversion SAME; subst. rewrite Nat.add_0_r; auto.
Qed.

Theorem store_path_prefix_invariant : forall ge cell P start count value final events target,
  store_path ge P start count (Returnstate value Kstop final) ->
  steps ge cell (live start) events target ->
  P (routine_memory target) /\ (length events <= S count)%nat.
Proof.
  intros ge cell P start count value final events target SCRIPT RUN.
  destruct (store_path_all _ _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[n [s [rest [COUNT [ES [TARGET TAIL]]]]]]|[n [m [COUNT [ES [TARGET GOOD]]]]]];
    subst; cbn.
  - split; [eapply store_path_initial; eassumption|rewrite repeat_length; lia].
  - split; [assumption|rewrite app_length, repeat_length; cbn; lia].
Qed.

Theorem store_path_defined_prefix : forall ge cell P start count value final events s,
  store_path ge P start count (Returnstate value Kstop final) ->
  steps ge cell (live start) events (live s) ->
  s = Returnstate value Kstop final \/
    exists next, step ge cell (live s) (source_step E0) (live next).
Proof.
  intros ge cell P start count value final events s SCRIPT RUN.
  destruct (store_path_all _ _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[n [s' [rest [COUNT [ES [TARGET TAIL]]]]]]|[n [m [_ [_ [TARGET _]]]]]];
    try discriminate.
  inversion TARGET; subst s'. inversion TAIL; subst; auto.
  right. destruct H0 as [IN [REAL _]]. exists next; apply internal; assumption.
Qed.

Theorem store_path_loss_every_prefix : forall ge cell P start count last n,
  store_path ge P start count last -> (n <= count)%nat ->
  exists mid, steps ge cell (live start) (repeat (source_step E0) n) (live mid) /\
    steps ge cell (live start) (repeat (source_step E0) n ++ [loss_step])
      (dead (memory_of mid)) /\ P (memory_of mid).
Proof.
  intros ge cell P start count last n SCRIPT. revert n.
  induction SCRIPT; intros j BOUND; destruct j; cbn.
  - exists s. split; [constructor|]. split; [econstructor; [constructor|constructor]|assumption].
  - lia.
  - exists s. split; [constructor|]. split; [econstructor; [constructor|constructor]|assumption].
  - destruct (IHSCRIPT j ltac:(lia)) as [mid [BEFORE [LOSS GOOD]]].
    exists mid. destruct H0 as [IN [REAL _]]. split.
    + econstructor; [apply internal; eassumption|exact BEFORE].
    + split; [econstructor; [apply internal; eassumption|exact LOSS]|exact GOOD].
Qed.

Lemma store_path_terminal_loss : forall ge cell P start count last,
  store_path ge P start count last ->
  steps ge cell (live start) (repeat (source_step E0) count ++ [loss_step])
    (dead (memory_of last)).
Proof.
  intros ge cell P start count last PATH; induction PATH; cbn.
  - econstructor; [constructor|constructor].
  - destruct H0 as [IN [REAL _]]. econstructor; [apply internal; eassumption|assumption].
Qed.
