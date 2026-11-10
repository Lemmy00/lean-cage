(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Guard cuts retain the actual executing function. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayGuardScope GatewayContexts.
Import ListNotations.

Definition gateway_guard_function (expected : function) (source : Clight.state) : Prop :=
  match source with
  | State actual _ _ _ _ _ => actual = expected
  | Returnstate _ Kstop _ => True
  | _ => False
  end.

Definition gateway_guard_function_state {World} expected (state : gateway_state World) : Prop :=
  match state with
  | gateway_live source _ => gateway_guard_function expected source
  | gateway_dead _ _ => True
  end.

Lemma gateway_guard_function_replace expected source memory :
  gateway_guard_function expected source ->
  gateway_guard_function expected (gateway_replace_memory source memory).
Proof. destruct source; cbn; auto. Qed.

Lemma gateway_guard_function_step {World Event} (backend : gateway_backend World Event) ge
    expected parameter value tail environment source world event target :
  gateway_guard_source parameter value (Kseq tail Kstop) environment source ->
  ~ gateway_guard_terminal (Kseq tail Kstop) source ->
  gateway_guard_function expected source ->
  gateway_step backend ge (gateway_live source world) event target ->
  gateway_guard_function_state expected target.
Proof.
  destruct source as [actual body continuation locals temporaries memory |
    definition arguments continuation memory | returned continuation memory];
    intros PROFILE TERMINAL FUNCTION STEP.
  - cbn in FUNCTION; subst actual.
    destruct PROFILE as [LOCALS [PARAMETER [BODY CONTINUATION]]].
    inversion STEP; subst; cbn [gateway_guard_function_state gateway_guard_function]; try exact I;
      try reflexivity.
    match goal with REAL : step2 _ _ _ _ |- _ => inversion REAL; subst end;
      cbn [gateway_guard_statement] in BODY; try contradiction; try reflexivity; try exact I.
    all: try match goal with BAD : gateway_guard_cont _ (Kseq _ Kstop) (Kcall _ _ _ _ _) |- _ => inversion BAD end.
    all: try match goal with CALL : is_call_cont ?kont |- _ =>
      exfalso; eapply gateway_guard_not_call_cont; [exact CONTINUATION | exact CALL] end.
    all: try match goal with CONT : gateway_guard_cont _ _ ?kont |- context [call_cont ?kont] =>
      rewrite (gateway_guard_call_cont _ _ _ CONT); exact I end.
  - contradiction.
  - destruct continuation; cbn in FUNCTION; try contradiction.
    exfalso; apply TERMINAL; right; exact I.
Qed.

(* A first terminal cut is needed: a later caller continuation need not have the
   original function. Both the cut and its retained identity come from one run. *)
Theorem gateway_guard_function_terminal_cut {World Event} (backend : gateway_backend World Event) ge
    ready (runtime : gateway_guard_runtime backend ready) expected parameter value tail environment
    source world events returned after next :
  ~ gateway_guard_statement parameter tail ->
  gateway_guard_source parameter value (Kseq tail Kstop) environment source ->
  gateway_guard_function expected source -> ready (memory_of source) world ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix reached reached_world,
    events = prefix ++ suffix /\
    gateway_steps backend ge (gateway_live source world) prefix (gateway_live reached reached_world) /\
    gateway_guard_source parameter value (Kseq tail Kstop) environment reached /\
    gateway_guard_function expected reached /\ ready (memory_of reached) reached_world /\
    gateway_guard_terminal (Kseq tail Kstop) reached /\
    gateway_steps backend ge (gateway_live reached reached_world) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intro OPAQUE; revert source world.
  induction events as [|event rest IH]; intros source world PROFILE FUNCTION READY RUN.
  - inversion RUN; subst.
    exists [], [], (Returnstate returned Kstop after), next.
    split; [reflexivity |]. split; [constructor |]. split; [exact PROFILE |].
    split; [exact I |]. split; [exact READY |]. split; [right; exact I | constructor].
  - destruct (gateway_guard_stop_or_continue parameter value tail environment source OPAQUE PROFILE)
      as [TERMINAL | [BOUNDARY RETURN]].
    + exists [], (event :: rest), source, world; cbn.
      split; [reflexivity |]. split; [constructor |]. split; [exact PROFILE |].
      split; [exact FUNCTION |]. split; [exact READY |]. split; assumption.
    + inversion RUN as [|first observed middle remaining last HEAD TAIL]; subst.
      assert (NOT_TERMINAL : ~ gateway_guard_terminal (Kseq tail Kstop) source).
      { intros [BAD | BAD]; contradiction. }
      assert (PRESERVED : gateway_guard_runtime_state parameter value (Kseq tail Kstop) environment ready middle).
      { eapply gateway_guard_runtime_step; [exact runtime | split; eassumption |
          exact NOT_TERMINAL | exact HEAD]. }
      assert (IDENTITY : gateway_guard_function_state expected middle).
      { eapply gateway_guard_function_step; eassumption. }
      destruct middle as [following current | memory current].
      * destruct PRESERVED as [FOLLOWING CURRENT].
        destruct (IH following current FOLLOWING IDENTITY CURRENT TAIL)
          as (prefix & suffix & reached & reached_world & EVENTS & PREFIX & SCOPE &
            IDENTITY_REACHED & REACHED & TERMINAL & SUFFIX).
        exists (event :: prefix), suffix, reached, reached_world.
        split; [cbn; congruence |]. split; [econstructor; eassumption |].
        split; [exact SCOPE |]. split; [exact IDENTITY_REACHED |].
        split; [exact REACHED |]. split; assumption.
      * destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ BAD]; discriminate.
Qed.
