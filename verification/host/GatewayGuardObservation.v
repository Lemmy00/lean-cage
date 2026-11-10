(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual guard prefixes contain no response-channel receives. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayGuardScope GatewayGuardFunction GatewayContexts
  GatewayStreamInterface.
Import ListNotations.

Lemma gateway_received_source_cons {Event} io descriptor trace (events : list (gateway_event Event)) :
  gateway_received_bytes io descriptor (gateway_source trace :: events) =
    gateway_received_bytes io descriptor events.
Proof. reflexivity. Qed.

Lemma gateway_guard_step_silent {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor (ready : mem -> World -> Prop)
    (silent_load : forall pointer before world result after next observed,
      ready before world -> gateway_builtin backend (EF_vload Mint32) [tptr (tvolatile tint)] [pointer]
        before world result after next observed -> io observed = None)
    parameter value tail environment source world event target :
  gateway_guard_source parameter value (Kseq tail Kstop) environment source ->
  ready (memory_of source) world ->
  gateway_step backend ge (gateway_live source world) event target ->
  gateway_received_event io descriptor event = [].
Proof.
  intros PROFILE READY STEP; inversion STEP; subst; try reflexivity; try contradiction.
  all: destruct PROFILE as [ENV [PARAMETER [BODY CONT]]].
  all: cbn [gateway_guard_statement] in BODY.
  all: destruct BODY as [DESTINATION [EF TYPES]]; subst ef types.
  all: match goal with ARGS : eval_exprlist _ _ _ _ _ [_] _ |- _ =>
    destruct (gateway_guard_one_argument _ _ _ _ _ _ _ ARGS) as [pointer VALUES]; subst values end.
  all: match goal with OPERATION : gateway_builtin _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (silent_load _ _ _ _ _ _ _ READY OPERATION) as IO end.
  all: unfold gateway_received_event; rewrite IO; reflexivity.
Qed.

Theorem gateway_guard_silent_terminal_cut {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor ready
    (runtime : gateway_guard_runtime backend ready)
    (silent_load : forall pointer before world result after next observed,
      ready before world -> gateway_builtin backend (EF_vload Mint32) [tptr (tvolatile tint)] [pointer]
        before world result after next observed -> io observed = None)
    expected parameter value tail environment source world events returned after next :
  ~ gateway_guard_statement parameter tail ->
  gateway_guard_source parameter value (Kseq tail Kstop) environment source ->
  gateway_guard_function expected source -> ready (memory_of source) world ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix reached reached_world,
    events = prefix ++ suffix /\ gateway_received_bytes io descriptor prefix = [] /\
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
    split; [reflexivity |]. split; [reflexivity |]. split; [constructor |]. split; [exact PROFILE |].
    split; [exact I |]. split; [exact READY |]. split; [right; exact I | constructor].
  - destruct (gateway_guard_stop_or_continue parameter value tail environment source OPAQUE PROFILE)
      as [TERMINAL | [BOUNDARY RETURN]].
    + exists [], (event :: rest), source, world; cbn.
      split; [reflexivity |]. split; [reflexivity |]. split; [constructor |]. split; [exact PROFILE |].
      split; [exact FUNCTION |]. split; [exact READY |]. split; assumption.
    + inversion RUN as [|first observed middle remaining last HEAD TAIL]; subst.
      assert (NOT_TERMINAL : ~ gateway_guard_terminal (Kseq tail Kstop) source).
      { intros [BAD | BAD]; contradiction. }
      assert (PRESERVED : gateway_guard_runtime_state parameter value (Kseq tail Kstop) environment ready middle).
      { eapply gateway_guard_runtime_step; [exact runtime | split; eassumption |
          exact NOT_TERMINAL | exact HEAD]. }
      assert (IDENTITY : gateway_guard_function_state expected middle).
      { eapply gateway_guard_function_step; eassumption. }
      assert (SILENT : gateway_received_event io descriptor event = []).
      { eapply gateway_guard_step_silent; eassumption. }
      destruct middle as [following current | memory current].
      * destruct PRESERVED as [FOLLOWING CURRENT].
        destruct (IH following current FOLLOWING IDENTITY CURRENT TAIL)
          as (prefix & suffix & reached & reached_world & EVENTS & EMPTY & PREFIX & SCOPE &
            IDENTITY_REACHED & REACHED & TERMINAL & SUFFIX).
        exists (event :: prefix), suffix, reached, reached_world.
        split; [cbn; congruence |]. split.
        -- change (gateway_received_event io descriptor event ++ gateway_received_bytes io descriptor prefix = []);
             rewrite SILENT, EMPTY; reflexivity.
        -- split; [econstructor; eassumption |].
           split; [exact SCOPE |]. split; [exact IDENTITY_REACHED |].
           split; [exact REACHED |]. split; assumption.
      * destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ BAD]; discriminate.
Qed.
