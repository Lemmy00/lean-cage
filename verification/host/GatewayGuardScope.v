(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Branching source guards retain their actual caller parameter. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayContexts.
Import ListNotations.

Fixpoint gateway_guard_statement (parameter : ident) (body : statement) : Prop :=
  match body with
  | Sskip | Sreturn _ => True
  | Sset identifier _ => identifier <> parameter
  | Ssequence first second | Sifthenelse _ first second =>
    gateway_guard_statement parameter first /\ gateway_guard_statement parameter second
  | Sbuiltin destination ef types _ => destination <> Some parameter /\
    ef = EF_vload Mint32 /\ types = [tptr (tvolatile tint)]
  | _ => False
  end.

Inductive gateway_guard_cont (parameter : ident) (boundary : cont) : cont -> Prop :=
  | gateway_guard_boundary_cont : gateway_guard_cont parameter boundary boundary
  | gateway_guard_sequence : forall body rest,
    gateway_guard_statement parameter body -> gateway_guard_cont parameter boundary rest ->
    gateway_guard_cont parameter boundary (Kseq body rest).

Lemma gateway_guard_call_cont parameter boundary continuation :
  gateway_guard_cont parameter boundary continuation -> call_cont continuation = call_cont boundary.
Proof. intro PROFILE; induction PROFILE; cbn; auto. Qed.

Lemma gateway_guard_not_call_cont parameter tail continuation :
  gateway_guard_cont parameter (Kseq tail Kstop) continuation -> ~ is_call_cont continuation.
Proof. intro PROFILE; induction PROFILE; cbn; tauto. Qed.

Definition gateway_guard_source (parameter : ident) (value : val) (boundary : cont)
    (environment : env) (source : Clight.state) : Prop :=
  match source with
  | State _ body continuation actual temporaries _ =>
    actual = environment /\ temporaries ! parameter = Some value /\
    gateway_guard_statement parameter body /\ gateway_guard_cont parameter boundary continuation
  | Returnstate _ Kstop _ => True
  | _ => False
  end.

Definition gateway_guard_boundary (boundary : cont) (source : Clight.state) : Prop :=
  match source with
  | State _ Sskip continuation _ _ _ => continuation = boundary
  | _ => False
  end.

Definition gateway_guard_return (source : Clight.state) : Prop :=
  match source with
  | State _ (Sreturn _) _ _ _ _ => True
  | Returnstate _ Kstop _ => True
  | _ => False
  end.

Definition gateway_guard_terminal boundary source : Prop :=
  gateway_guard_boundary boundary source \/ gateway_guard_return source.

Definition control_entry_guard := match fn_body f_host_control with
  | Ssequence guard _ => guard | _ => Sskip end.
Definition control_after_guard := match fn_body f_host_control with
  | Ssequence _ after => after | _ => Sskip end.

Lemma actual_control_guard_classification : gateway_guard_statement _stream control_entry_guard.
Proof. cbn; intuition discriminate. Qed.

Lemma actual_control_after_guard_is_mutating : ~ gateway_guard_statement _stream control_after_guard.
Proof. cbn; tauto. Qed.

Lemma gateway_guard_stop_or_continue parameter value tail environment source :
  ~ gateway_guard_statement parameter tail ->
  gateway_guard_source parameter value (Kseq tail Kstop) environment source ->
  gateway_guard_terminal (Kseq tail Kstop) source \/
    (~ gateway_guard_boundary (Kseq tail Kstop) source /\ ~ gateway_guard_return source).
Proof.
  intros OPAQUE PROFILE.
  destruct source as [function body continuation actual temporaries memory |
    definition arguments continuation memory | returned continuation memory].
  - destruct PROFILE as [ENV [PARAM [BODY CONT]]].
    destruct body; try solve [right; cbn; tauto].
    + inversion CONT; subst.
      * left; left; reflexivity.
      * right; split; [| cbn; tauto].
        cbn; intro SAME; inversion SAME; subst; contradiction.
    + left; right; exact I.
  - contradiction.
  - destruct continuation; cbn in PROFILE; try contradiction; left; right; exact I.
Qed.

(* The guard can read the current cancellation flag, but cannot overwrite the
   source stream parameter or perform a data-channel receive operation. *)
Lemma gateway_guard_internal_step ge parameter value boundary environment source trace after :
  call_cont boundary = Kstop -> (exists tail, boundary = Kseq tail Kstop) ->
  gateway_guard_source parameter value boundary environment source ->
  ~ gateway_guard_boundary boundary source -> internal_state source ->
  step2 ge source trace after ->
  gateway_guard_source parameter value boundary environment after /\
    (memory_of after = memory_of source \/
      exists returned, after = Returnstate returned Kstop (memory_of after) /\
        Mem.free_list (memory_of source) (blocks_of_env ge environment) = Some (memory_of after)).
Proof.
  destruct source as [function body continuation actual temporaries memory |
    definition arguments continuation memory | returned continuation memory];
    intros STOP [tail SHAPE] PROFILE BOUNDARY INTERNAL STEP; subst boundary.
  - destruct PROFILE as [ENV [PARAM [BODY CONT]]]; subst actual.
    inversion STEP; subst; cbn [gateway_guard_statement] in BODY; try contradiction.
    all: try solve [cbn [internal_state] in INTERNAL; contradiction].
    all: try match goal with BAD : gateway_guard_cont _ (Kseq _ Kstop) (Kloop1 _ _ _) |- _ => inversion BAD end.
    all: try match goal with BAD : gateway_guard_cont _ (Kseq _ Kstop) (Kloop2 _ _ _) |- _ => inversion BAD end.
    all: try match goal with BAD : gateway_guard_cont _ (Kseq _ Kstop) (Kswitch _) |- _ => inversion BAD end.
    all: try match goal with BAD : gateway_guard_cont _ (Kseq _ Kstop) Kstop |- _ => inversion BAD end.
    all: try match goal with CALL : is_call_cont ?kont |- _ =>
      exfalso; eapply gateway_guard_not_call_cont; [exact CONT | exact CALL]
    end.
    + split.
      * cbn; split; [reflexivity |]. split.
        -- rewrite PTree.gso; [exact PARAM | congruence].
        -- split; [exact I | exact CONT].
      * left; reflexivity.
    + destruct BODY as [FIRST SECOND]; split.
      * cbn; split; [reflexivity |]. split; [exact PARAM |].
        split; [exact FIRST | apply gateway_guard_sequence; assumption].
      * left; reflexivity.
    + inversion CONT; subst.
      * exfalso; apply BOUNDARY; reflexivity.
      * split; [cbn; repeat split; assumption | left; reflexivity].
    + destruct BODY as [FIRST SECOND]; destruct b; split;
        [cbn; repeat split; assumption | left; reflexivity |
         cbn; repeat split; assumption | left; reflexivity].
    + rewrite (gateway_guard_call_cont _ _ _ CONT), STOP.
      split; [exact I |]. right; eexists; split; [reflexivity | eassumption].
    + rewrite (gateway_guard_call_cont _ _ _ CONT), STOP.
      split; [exact I |]. right; eexists; split; [reflexivity | eassumption].

  - contradiction.
  - destruct continuation; cbn in PROFILE; try contradiction; inversion STEP.
Qed.

Lemma gateway_guard_internal_quiet ge parameter value tail environment source trace after :
  gateway_guard_source parameter value (Kseq tail Kstop) environment source ->
  ~ gateway_guard_boundary (Kseq tail Kstop) source -> ~ gateway_guard_return source ->
  internal_state source -> step2 ge source trace after -> memory_of after = memory_of source.
Proof.
  destruct source as [function body continuation actual temporaries memory |
    definition arguments continuation memory | returned continuation memory];
    intros PROFILE BOUNDARY RETURN INTERNAL STEP.
  - destruct PROFILE as [ENV [PARAM [BODY CONT]]]; subst actual.
    destruct body; cbn [gateway_guard_statement] in BODY;
      cbn [gateway_guard_return] in RETURN; try contradiction;
      cbn [internal_state] in INTERNAL; try contradiction;
      inversion STEP; subst; try reflexivity; try contradiction.
    exfalso; eapply gateway_guard_not_call_cont; [exact CONT | eassumption].
  - contradiction.
  - destruct continuation; cbn in PROFILE; try contradiction; cbn in RETURN; contradiction.
Qed.

Lemma gateway_guard_source_replace parameter value boundary environment source memory :
  gateway_guard_source parameter value boundary environment source ->
  gateway_guard_source parameter value boundary environment (gateway_replace_memory source memory).
Proof.
  destruct source as [function body continuation actual temporaries original |
    definition arguments continuation original | returned continuation original].
  - cbn; tauto.
  - cbn; tauto.
  - destruct continuation; cbn; tauto.
Qed.

Lemma gateway_guard_parameter_retained parameter value destination result temporaries :
  destination <> Some parameter -> temporaries ! parameter = Some value ->
  (set_opttemp destination result temporaries) ! parameter = Some value.
Proof.
  destruct destination as [identifier |]; cbn; intros DIFFERENT PARAM; [| exact PARAM].
  rewrite PTree.gso; [exact PARAM | congruence].
Qed.

(* These are two individual primitive obligations. The same actual program must
   establish the raw cells/ownership needed to instantiate them at each call. *)
Record gateway_guard_runtime {World Event} (backend : gateway_backend World Event)
    (ready : mem -> World -> Prop) : Prop := {
  gateway_guard_ambient_ready : forall before world after next,
    ready before world -> gateway_interference backend before world after next -> ready after next;
  gateway_guard_vload_ready : forall pointer before world result after next observed,
    ready before world ->
    gateway_builtin backend (EF_vload Mint32) [tptr (tvolatile tint)] [pointer]
      before world result after next observed -> ready after next
}.

Lemma gateway_guard_one_argument ge environment temporaries memory arguments ty values :
  eval_exprlist ge environment temporaries memory arguments [ty] values ->
  exists value, values = [value].
Proof.
  intro EVALUATION; inversion EVALUATION; subst.
  match goal with TAIL : eval_exprlist _ _ _ _ _ [] _ |- _ => inversion TAIL; subst end.
  eexists; reflexivity.
Qed.

Definition gateway_guard_runtime_state {World} parameter value boundary environment
    (ready : mem -> World -> Prop) (state : gateway_state World) : Prop :=
  match state with
  | gateway_live source world => gateway_guard_source parameter value boundary environment source /\
    ready (memory_of source) world
  | gateway_dead _ _ => True
  end.

Lemma gateway_guard_runtime_step {World Event} (backend : gateway_backend World Event) ge
    ready (runtime : gateway_guard_runtime backend ready)
    parameter value tail environment source world event target :
  gateway_guard_runtime_state parameter value (Kseq tail Kstop) environment ready (gateway_live source world) ->
  ~ gateway_guard_terminal (Kseq tail Kstop) source ->
  gateway_step backend ge (gateway_live source world) event target ->
  gateway_guard_runtime_state parameter value (Kseq tail Kstop) environment ready target.
Proof.
  intros [PROFILE READY] NOT_TERMINAL STEP.
  assert (BOUNDARY : ~ gateway_guard_boundary (Kseq tail Kstop) source) by (intro BAD; apply NOT_TERMINAL; left; exact BAD).
  assert (RETURN : ~ gateway_guard_return source) by (intro BAD; apply NOT_TERMINAL; right; exact BAD).
  inversion STEP; subst; cbn [gateway_guard_runtime_state]; try exact I.
  - match goal with INTERNAL : internal_state ?original, REAL : step2 ge ?original ?trace ?following |- _ =>
      pose proof (gateway_guard_internal_quiet ge parameter value tail environment original trace following
        PROFILE BOUNDARY RETURN INTERNAL REAL) as MEMORY;
      destruct (gateway_guard_internal_step ge parameter value (Kseq tail Kstop) environment original trace following
        eq_refl ltac:(eexists; reflexivity) PROFILE BOUNDARY INTERNAL REAL) as [NEXT CHANGED]
    end.
    split; [exact NEXT |]. rewrite MEMORY; exact READY.

  - contradiction.
  - destruct PROFILE as [ENV [PARAM [BODY CONT]]]; subst.
    cbn [gateway_guard_statement] in BODY.
    destruct BODY as [DESTINATION [EF TYPES]]; subst ef types.
    match goal with ARGS : eval_exprlist _ _ _ _ _ [_] _ |- _ =>
      destruct (gateway_guard_one_argument _ _ _ _ _ _ _ ARGS) as [pointer VALUES]; subst values end.
    split.
    + cbn; split; [reflexivity |]. split.
      * eapply gateway_guard_parameter_retained; eassumption.
      * split; [exact I | exact CONT].
    + eapply gateway_guard_vload_ready; [exact runtime | exact READY | eassumption].
  - split; [apply gateway_guard_source_replace; exact PROFILE |].
    rewrite gateway_replace_memory_of.
    eapply gateway_guard_ambient_ready; [exact runtime | exact READY | eassumption].
  - split; assumption.
Qed.

(* §FS-host-boundary.caller: The actual guard either returns or reaches its next real phase. *)
Theorem gateway_guard_terminal_cut {World Event} (backend : gateway_backend World Event) ge
    ready (runtime : gateway_guard_runtime backend ready) parameter value tail environment
    source world events returned after next :
  ~ gateway_guard_statement parameter tail ->
  gateway_guard_source parameter value (Kseq tail Kstop) environment source ->
  ready (memory_of source) world ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix reached reached_world,
    events = prefix ++ suffix /\
    gateway_steps backend ge (gateway_live source world) prefix (gateway_live reached reached_world) /\
    gateway_guard_source parameter value (Kseq tail Kstop) environment reached /\
    ready (memory_of reached) reached_world /\ gateway_guard_terminal (Kseq tail Kstop) reached /\
    gateway_steps backend ge (gateway_live reached reached_world) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intro OPAQUE; revert source world.
  induction events as [|event rest IH]; intros source world PROFILE READY RUN.
  - inversion RUN; subst.
    exists [], [], (Returnstate returned Kstop after), next.
    split; [reflexivity |]. split; [constructor |]. split; [exact PROFILE |].
    split; [exact READY |]. split; [right; exact I | constructor].
  - destruct (gateway_guard_stop_or_continue parameter value tail environment source OPAQUE PROFILE)
      as [TERMINAL | [BOUNDARY RETURN]].
    + exists [], (event :: rest), source, world; cbn.
      split; [reflexivity |]. split; [constructor |]. split; [exact PROFILE |].
      split; [exact READY |]. split; assumption.
    + inversion RUN as [|first observed middle remaining last HEAD TAIL]; subst.
      assert (PRESERVED : gateway_guard_runtime_state parameter value (Kseq tail Kstop) environment ready middle).
      { eapply gateway_guard_runtime_step; [exact runtime | split; eassumption | | exact HEAD].
        intros [BAD | BAD]; contradiction. }
      destruct middle as [following current | memory current].
      * destruct PRESERVED as [FOLLOWING CURRENT].
        destruct (IH following current FOLLOWING CURRENT TAIL)
          as [prefix [suffix [reached [reached_world [EVENTS [PREFIX [SCOPE [REACHED [TERMINAL SUFFIX]]]]]]]]].
        exists (event :: prefix), suffix, reached, reached_world.
        split; [cbn; congruence |]. split; [econstructor; eassumption |].
        split; [exact SCOPE |]. split; [exact REACHED |]. split; assumption.
      * destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ BAD]; discriminate.
Qed.
