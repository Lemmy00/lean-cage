(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.continuation: Actual continuation replacement, including nested calls. *)
From Coq Require Import List.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine LibraryMachine.
Import ListNotations.

Fixpoint plug_cont (k suffix : cont) : cont :=
  match k with
  | Kstop => suffix
  | Kseq s rest => Kseq s (plug_cont rest suffix)
  | Kloop1 a b rest => Kloop1 a b (plug_cont rest suffix)
  | Kloop2 a b rest => Kloop2 a b (plug_cont rest suffix)
  | Kswitch rest => Kswitch (plug_cont rest suffix)
  | Kcall opt f e le rest => Kcall opt f e le (plug_cont rest suffix)
  end.
Definition plug_state (s : Clight.state) suffix :=
  match s with
  | State f stmt k e le m => State f stmt (plug_cont k suffix) e le m
  | Callstate fd args k m => Callstate fd args (plug_cont k suffix) m
  | Returnstate value k m => Returnstate value (plug_cont k suffix) m
  end.
Definition plug_machine s suffix :=
  match s with live source => live (plug_state source suffix) | dead m => dead m end.
Definition local_return s := exists value m, s = Returnstate value Kstop m.

Lemma plug_memory : forall s suffix, memory_of (plug_state s suffix) = memory_of s.
Proof. destruct s; reflexivity. Qed.
Lemma plug_internal : forall s suffix, internal_state (plug_state s suffix) = internal_state s.
Proof. destruct s; reflexivity. Qed.
Lemma plug_call_cont : forall k suffix, is_call_cont suffix ->
  call_cont (plug_cont k suffix) = plug_cont (call_cont k) suffix.
Proof. induction k; intros suffix CALL; cbn; auto. destruct suffix; cbn in *; tauto. Qed.
Lemma plug_is_call_cont : forall k suffix, is_call_cont suffix ->
  (is_call_cont (plug_cont k suffix) <-> is_call_cont k).
Proof. destruct k; cbn; intros; tauto. Qed.

Lemma plug_find_label : forall lbl stmt k suffix,
  find_label lbl stmt (plug_cont k suffix) =
    option_map (fun sk => (fst sk, plug_cont (snd sk) suffix)) (find_label lbl stmt k)
with plug_find_label_ls : forall lbl stmts k suffix,
  find_label_ls lbl stmts (plug_cont k suffix) =
    option_map (fun sk => (fst sk, plug_cont (snd sk) suffix)) (find_label_ls lbl stmts k).
Proof.
  - intros lbl stmt k suffix; destruct stmt; cbn; try reflexivity.
    + change (Kseq stmt2 (plug_cont k suffix)) with (plug_cont (Kseq stmt2 k) suffix).
      rewrite plug_find_label. destruct (find_label lbl stmt1 (Kseq stmt2 k)) as [[s rest]|]; cbn; auto.
    + rewrite plug_find_label. destruct (find_label lbl stmt1 k) as [[s rest]|]; cbn; auto.
    + change (Kloop1 stmt1 stmt2 (plug_cont k suffix)) with (plug_cont (Kloop1 stmt1 stmt2 k) suffix).
      rewrite plug_find_label. destruct (find_label lbl stmt1 (Kloop1 stmt1 stmt2 k)) as [[s rest]|]; cbn; auto.
      change (Kloop2 stmt1 stmt2 (plug_cont k suffix)) with (plug_cont (Kloop2 stmt1 stmt2 k) suffix).
      apply plug_find_label.
    + change (Kswitch (plug_cont k suffix)) with (plug_cont (Kswitch k) suffix).
      apply plug_find_label_ls.
    + destruct (ident_eq lbl l); cbn; auto.
  - intros lbl stmts k suffix; destruct stmts; cbn; try reflexivity.
    change (Kseq (seq_of_labeled_statement stmts) (plug_cont k suffix)) with (plug_cont (Kseq (seq_of_labeled_statement stmts) k) suffix).
    rewrite plug_find_label. destruct (find_label lbl s (Kseq (seq_of_labeled_statement stmts) k)) as [[stmt rest]|]; cbn; auto.
Qed.

Theorem plug_clight_step : forall ge s t next suffix,
  is_call_cont suffix -> step2 ge s t next ->
  step2 ge (plug_state s suffix) t (plug_state next suffix).
Proof.
  intros ge s t next suffix CALL STEP. inversion STEP; subst; cbn;
    try solve [econstructor; eassumption].
  - rewrite <- plug_call_cont by assumption. econstructor; eassumption.
  - rewrite <- plug_call_cont by assumption. econstructor; eassumption.
  - apply step_skip_call; [apply (proj2 (plug_is_call_cont _ _ CALL)); assumption|assumption].
  - eapply step_goto. rewrite plug_call_cont, plug_find_label by assumption.
    match goal with H : find_label _ _ _ = _ |- _ => rewrite H end. reflexivity.
Qed.

Lemma plug_cont_stop : forall k, plug_cont k Kstop = k.
Proof. induction k; cbn; congruence. Qed.
Lemma plug_state_stop : forall s, plug_state s Kstop = s.
Proof. destruct s; cbn; rewrite plug_cont_stop; reflexivity. Qed.

Theorem unplug_clight_step : forall ge s t target suffix,
  is_call_cont suffix -> ~ local_return s ->
  step2 ge (plug_state s suffix) t target ->
  exists next, step2 ge s t next /\ target = plug_state next suffix.
Proof.
  intros ge s t target suffix CALL NOTRETURN STEP.
  destruct suffix as [|st suf|a b suf|a b suf|suf|opt caller ce cl suf]; cbn in CALL; try contradiction.
  { rewrite plug_state_stop in STEP. exists target; rewrite plug_state_stop; auto. }
  destruct s as [f stmt k e le m|fd args k m|value k m].
  - destruct k; cbn in STEP; inversion STEP; subst;
      try solve [eexists; split; [econstructor; eassumption|cbn; reflexivity]].
    all: try solve [eexists; split;
      [eapply step_return_0; eassumption|cbn; rewrite plug_call_cont by exact I; reflexivity]].
    all: try solve [eexists; split;
      [eapply step_return_1; eassumption|cbn; rewrite plug_call_cont by exact I; reflexivity]].
    all: try solve [eexists; split;
      [eapply step_skip_call; [exact I|eassumption]|cbn; reflexivity]].
    all: try solve [match goal with H : is_call_cont _ |- _ => contradiction H end].
    all: match goal with
    | LABEL : find_label ?lbl (fn_body ?func) _ = Some (?body,?kont)
      |- exists next, step2 _ (State _ _ ?original _ _ _) _ next /\ _ =>
      assert (FOUNDPLUG : find_label lbl (fn_body func)
        (plug_cont (call_cont original) (Kcall opt caller ce cl suf)) = Some (body,kont))
        by (rewrite <- plug_call_cont by exact I; exact LABEL);
      rewrite plug_find_label in FOUNDPLUG;
      destruct (find_label lbl (fn_body func) (call_cont original)) as [[a b]|] eqn:FOUND;
      cbn in FOUNDPLUG; try discriminate; inversion FOUNDPLUG; subst;
      eexists; split; [eapply step_goto; exact FOUND|cbn; reflexivity]
    end.
  - cbn in STEP; inversion STEP; subst.
    + eexists; split; [apply step_internal_function; eassumption|cbn; reflexivity].
    + eexists; split; [apply step_external_function; eassumption|cbn; reflexivity].
  - destruct k; cbn in STEP.
    { exfalso; apply NOTRETURN; repeat eexists. }
    all: inversion STEP; subst; try solve [eexists; split; [constructor|reflexivity]].
Qed.

Lemma plug_boundary : forall cell s q suffix,
  boundary cell (plug_state s suffix) q <-> boundary cell s q.
Proof.
  intros cell s q suffix; split; intros BOUND.
  - destruct s; cbn in BOUND; inversion BOUND; subst; constructor; assumption.
  - inversion BOUND; subst; cbn; constructor; assumption.
Qed.

Theorem plug_machine_step : forall ge cell s ev next suffix,
  is_call_cont suffix -> Machine.step ge cell s ev next ->
  Machine.step ge cell (plug_machine s suffix) ev (plug_machine next suffix).
Proof.
  intros ge cell s ev next suffix CALL STEP; inversion STEP; subst; cbn.
  - apply internal; [rewrite plug_internal; assumption|apply plug_clight_step; assumption].
  - apply effect; [inversion H; subst; constructor; assumption|assumption].
  - apply errno_address; assumption.
  - apply waiting with q; [apply (proj2 (plug_boundary _ _ _ suffix)); assumption|rewrite plug_memory; assumption].
  - rewrite <- plug_memory with (suffix:=suffix); constructor.
  - apply lose_during_io; [inversion H; subst; constructor; assumption|assumption].
Qed.

Theorem unplug_machine_step : forall ge cell s ev target suffix,
  is_call_cont suffix -> ~ local_return s ->
  Machine.step ge cell (live (plug_state s suffix)) ev target ->
  exists next, Machine.step ge cell (live s) ev next /\ target = plug_machine next suffix.
Proof.
  intros ge cell s ev target suffix CALL NOTRETURN STEP; inversion STEP; subst.
  - destruct (unplug_clight_step ge s t s' suffix CALL NOTRETURN H1) as [next [REAL SAME]].
    exists (live next); split; [apply internal; [rewrite <- (plug_internal s suffix); exact H0|exact REAL]|cbn; congruence].
  - destruct s; cbn in *; try discriminate; inversion H; subst.
    eexists; split; [eapply effect; [inversion H0; subst; constructor; assumption|eassumption]|reflexivity].
  - destruct s; cbn in *; try discriminate; inversion H; subst.
    eexists; split; [apply errno_address; eassumption|reflexivity].
  - exists (live s); split; [eapply waiting; [apply (proj1 (plug_boundary _ _ _ suffix)); eassumption|rewrite <- (plug_memory s suffix); eassumption]|reflexivity].
  - exists (dead (memory_of s)); split; [constructor|cbn; rewrite plug_memory; reflexivity].
  - destruct s; cbn in *; try discriminate; inversion H; subst.
    eexists; split; [eapply lose_during_io; [inversion H0; subst; constructor; assumption|eassumption]|reflexivity].
Qed.

Lemma plug_library_ready : forall cell s suffix,
  library_ready cell (plug_state s suffix) <-> library_ready cell s.
Proof.
  intros cell s suffix; split; intros READY.
  - destruct s; cbn in READY; inversion READY; subst; constructor; assumption.
  - inversion READY; subst; cbn; constructor; assumption.
Qed.

Theorem plug_library_step : forall ge cell s ev next suffix,
  is_call_cont suffix -> library_step ge cell s ev next ->
  library_step ge cell (plug_machine s suffix) ev (plug_machine next suffix).
Proof.
  intros ge cell s ev next suffix CALL STEP; inversion STEP; subst; cbn;
    try solve [econstructor; eassumption].
  - apply original_step. apply plug_machine_step; assumption.
  - apply library_wait_step. apply (proj2 (plug_library_ready _ _ suffix)); assumption.
Qed.

Theorem unplug_library_step : forall ge cell s ev target suffix,
  is_call_cont suffix -> ~ local_return s ->
  library_step ge cell (live (plug_state s suffix)) ev target ->
  exists next, library_step ge cell (live s) ev next /\ target = plug_machine next suffix.
Proof.
  intros ge cell s ev target suffix CALL NOTRETURN STEP; inversion STEP; subst.
  - match goal with OLD : Machine.step _ _ _ _ _ |- _ =>
      destruct (unplug_machine_step _ _ _ _ _ _ CALL NOTRETURN OLD) as [next [REAL SAME]] end.
    exists next; split; [constructor; exact REAL|exact SAME].
  - destruct s; cbn in *; try discriminate; inversion H; subst.
    eexists; split; [apply strcmp_step; eassumption|reflexivity].
  - destruct s; cbn in *; try discriminate; inversion H; subst.
    eexists; split; [apply memcmp_step; eassumption|reflexivity].
  - destruct s; cbn in *; try discriminate; inversion H; subst.
    eexists; split; [apply memcpy_step; eassumption|reflexivity].
  - destruct s; cbn in *; try discriminate; inversion H; subst.
    eexists; split; [eapply memcpy_loss_step; eassumption|reflexivity].
  - destruct s; cbn in *; try discriminate; inversion H; subst.
    eexists; split; [apply close_step; eassumption|reflexivity].
  - destruct s; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply exit_step|reflexivity].
  - exists (live s); split; [apply library_wait_step; apply (proj1 (plug_library_ready _ _ suffix)); assumption|reflexivity].
Qed.

Theorem plug_library_steps : forall ge cell s events next suffix,
  is_call_cont suffix -> library_steps ge cell s events next ->
  library_steps ge cell (plug_machine s suffix) events (plug_machine next suffix).
Proof.
  intros ge cell s events next suffix CALL RUN; induction RUN; [constructor|].
  econstructor; [apply plug_library_step; eassumption|exact IHRUN].
Qed.

Lemma local_return_dec : forall s, {local_return s} + {~ local_return s}.
Proof.
  destruct s as [f stmt k e le m|fd args k m|value k m]; try solve [right; intros [v [m' EQ]]; discriminate].
  destruct k; try solve [right; intros [v [m' EQ]]; discriminate].
  left; repeat eexists.
Qed.

Require Import LibraryPreservation.
Theorem caller_run_decomposition : forall ge cell suffix start events target,
  is_call_cont suffix ->
  library_steps ge cell (live (plug_state start suffix)) events target ->
  (exists local_target, library_steps ge cell (live start) events local_target /\
    target = plug_machine local_target suffix) \/
  (exists before after value m, events = before ++ after /\
    library_steps ge cell (live start) before (live (Returnstate value Kstop m)) /\
    library_steps ge cell (live (Returnstate value suffix m)) after target).
Proof.
  intros ge cell suffix start events; revert start.
  induction events as [|ev rest IH]; intros start target CALL RUN.
  - inversion RUN; subst. left. exists (live start); split; [constructor|reflexivity].
  - destruct (local_return_dec start) as [[value [m EQ]]|NOTRETURN].
    + subst. right; exists [], (ev::rest), value, m; split; [reflexivity|].
      split; [constructor|exact RUN].
    + inversion RUN; subst.
      match goal with STEP : library_step _ _ _ _ _ |- _ =>
        destruct (unplug_library_step _ _ _ _ _ _ CALL NOTRETURN STEP) as [local_mid [REAL SAME]] end.
      subst mid. destruct local_mid as [next|m]; cbn in *.
      * match goal with TAIL : library_steps _ _ (live (plug_state next suffix)) _ _ |- _ =>
          destruct (IH next target CALL TAIL) as [[last [LOCAL EQ]]|
            [before [after [value [m [ES [LOCAL TAILCALL]]]]]]] end.
        -- left; exists last; split; [econstructor; eassumption|assumption].
        -- right; exists (ev::before), after, value, m. split; [cbn; congruence|].
           split; [econstructor; eassumption|assumption].
      * match goal with TAIL : library_steps _ _ (dead m) _ _ |- _ =>
          destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES EQ] end.
        subst. left; exists (dead m); split; [econstructor; [exact REAL|constructor]|reflexivity].
Qed.
