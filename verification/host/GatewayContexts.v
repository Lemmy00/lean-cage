(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Preserve worlds and effects across caller contexts. *)
From Stdlib Require Import List Lia.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewayMachine.
Import ListNotations.

Definition gateway_plug {World}(state:gateway_state World)(suffix:cont) : gateway_state World :=
  match state with
  | gateway_live source world =>gateway_live(plug_state source suffix)world
  | gateway_dead memory world =>gateway_dead memory world
  end.

Lemma gateway_replace_memory_plug source memory suffix :
  gateway_replace_memory(plug_state source suffix)memory =
    plug_state(gateway_replace_memory source memory)suffix.
Proof. destruct source;reflexivity. Qed.

Lemma gateway_primitive_plug source suffix :
  gateway_at_primitive(plug_state source suffix)<->gateway_at_primitive source.
Proof. destruct source;reflexivity. Qed.

Theorem gateway_plug_step {World Event}(backend:gateway_backend World Event)ge before event after suffix :
  is_call_cont suffix ->gateway_step backend ge before event after ->
  gateway_step backend ge(gateway_plug before suffix)event(gateway_plug after suffix).
Proof.
  intros CALL STEP;inversion STEP;subst;cbn.
  - apply gateway_internal;[rewrite plug_internal;assumption|apply plug_clight_step;assumption].
  - apply gateway_external_returned;assumption.
  - eapply gateway_builtin_returned;eassumption.
  - rewrite <-gateway_replace_memory_plug.
    apply gateway_interleaved;rewrite plug_memory;assumption.
  - apply gateway_waiting;apply(proj2(gateway_primitive_plug _ _));assumption.
  - rewrite <-plug_memory with(suffix:=suffix);apply gateway_process_lost.
  - eapply gateway_external_committed_lost;eassumption.
  - eapply gateway_builtin_committed_lost;eassumption.
Qed.

Theorem gateway_unplug_step {World Event}(backend:gateway_backend World Event)ge source world event after suffix :
  is_call_cont suffix ->~local_return source ->
  gateway_step backend ge(gateway_live(plug_state source suffix)world)event after ->
  exists next,gateway_step backend ge(gateway_live source world)event next /\
    after=gateway_plug next suffix.
Proof.
  intros CALL NOTRETURN STEP;inversion STEP;subst.
  - match goal with ORIGINAL:step2 _ _ _ _|-_=>
      destruct(unplug_clight_step _ _ _ _ _ CALL NOTRETURN ORIGINAL)as[local_next[REAL SAME]]end.
    eexists;split.
    + apply gateway_internal;[rewrite <-plug_internal with(suffix:=suffix);eassumption|exact REAL].
    + cbn;congruence.
  - destruct source;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply gateway_external_returned;eassumption|reflexivity].
  - destruct source;cbn in *;try discriminate.
    match goal with EQ:State _ _ _ _ _ _=State _ _ _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[eapply gateway_builtin_returned;eassumption|reflexivity].
  - exists(gateway_live(gateway_replace_memory source after0)next);split.
    + apply gateway_interleaved;rewrite <-plug_memory with(suffix:=suffix);eassumption.
    + cbn;rewrite gateway_replace_memory_plug;reflexivity.
  - exists(gateway_live source world);split.
    + apply gateway_waiting;apply(proj1(gateway_primitive_plug source suffix));assumption.
    + reflexivity.
  - exists(gateway_dead(memory_of source)world);split.
    + apply gateway_process_lost.
    + cbn;rewrite plug_memory;reflexivity.
  - destruct source;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[eapply gateway_external_committed_lost;eassumption|reflexivity].
  - destruct source;cbn in *;try discriminate.
    match goal with EQ:State _ _ _ _ _ _=State _ _ _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[eapply gateway_builtin_committed_lost;eassumption|reflexivity].
Qed.

Theorem gateway_plug_steps {World Event}(backend:gateway_backend World Event)ge before events after suffix :
  is_call_cont suffix ->gateway_steps backend ge before events after ->
  gateway_steps backend ge(gateway_plug before suffix)events(gateway_plug after suffix).
Proof.
  intros CALL RUN;induction RUN;[constructor|].
  econstructor;[apply gateway_plug_step;eassumption|exact IHRUN].
Qed.

Lemma gateway_dead_steps {World Event}(backend:gateway_backend World Event)ge memory world events target :
  gateway_steps backend ge(gateway_dead memory world)events target ->
  events=[] /\target=gateway_dead memory world.
Proof.
  intro RUN;inversion RUN;subst;[auto|].
  match goal with STEP:gateway_step _ _ (gateway_dead _ _)_ _|-_=>inversion STEP end.
Qed.

(* §FS-host-boundary.caller: A caller cut retains the actual callee effects and returned world. *)
Theorem gateway_caller_run_decomposition {World Event}(backend:gateway_backend World Event)ge
    suffix start world events target :
  is_call_cont suffix ->
  gateway_steps backend ge(gateway_live(plug_state start suffix)world)events target ->
  (exists local_target,gateway_steps backend ge(gateway_live start world)events local_target /\
    target=gateway_plug local_target suffix) \/
  (exists before after value memory returned_world,
    events=before++after /\
    gateway_steps backend ge(gateway_live start world)before
      (gateway_live(Returnstate value Kstop memory)returned_world) /\
    gateway_steps backend ge(gateway_live(Returnstate value suffix memory)returned_world)after target).
Proof.
  revert start world;induction events as[|event rest IH];intros start world CALL RUN.
  - inversion RUN;subst;left;exists(gateway_live start world);split;[constructor|reflexivity].
  - destruct(local_return_dec start)as[[value[memory SAME]]|NOTRETURN].
    + subst;right;exists[],(event::rest),value,memory,world;split;[reflexivity|].
      split;[constructor|exact RUN].
    + inversion RUN;subst.
      match goal with STEP:gateway_step _ _ _ _ _|-_=>
        destruct(gateway_unplug_step _ _ _ _ _ _ _ CALL NOTRETURN STEP)
          as[local_middle[REAL SAME]]end.
      subst middle;destruct local_middle as[next next_world|memory next_world];cbn in *.
      * match goal with TAIL:gateway_steps _ _ (gateway_live(plug_state next suffix)next_world)_ _|-_=>
          destruct(IH next next_world CALL TAIL)as[[last[LOCAL SAME]]|
            [before[after[value[returned_memory[returned_world[EVENTS[LOCAL CONTINUE]]]]]]]]end.
        -- left;exists last;split;[econstructor;eassumption|exact SAME].
        -- right;exists(event::before),after,value,returned_memory,returned_world.
           split;[cbn;congruence|]. split;[econstructor;eassumption|exact CONTINUE].
      * match goal with TAIL:gateway_steps _ _ (gateway_dead memory next_world)_ _|-_=>
          destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[EVENTS SAME]end.
        subst;left;exists(gateway_dead memory next_world);split.
        -- econstructor;[exact REAL|constructor].
        -- reflexivity.
Qed.

Fixpoint gateway_statement_weight (source:statement) : nat :=
  match source with
  |Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
    S(gateway_statement_weight first+gateway_statement_weight rest)
  |Sswitch _ labels=>S(gateway_labels_weight labels)
  |Slabel _ body=>S(gateway_statement_weight body)
  |_=>1
  end
with gateway_labels_weight (source:labeled_statements) : nat :=
  match source with
  |LSnil=>0
  |LScons _ body rest=>S(gateway_statement_weight body+gateway_labels_weight rest)
  end.

Fixpoint gateway_cont_weight (continuation:cont) : nat :=
  match continuation with
  |Kstop=>0
  |Kseq body rest=>S(gateway_statement_weight body+gateway_cont_weight rest)
  |Kloop1 first second rest|Kloop2 first second rest=>
    S(gateway_statement_weight first+gateway_statement_weight second+gateway_cont_weight rest)
  |Kswitch rest|Kcall _ _ _ _ rest=>S(gateway_cont_weight rest)
  end.

Definition gateway_continuation (source:Clight.state) : cont :=
  match source with
  |State _ _ continuation _ _ _|Callstate _ _ continuation _|Returnstate _ continuation _=>continuation
  end.

Lemma gateway_plug_cont_weight local suffix :
  gateway_cont_weight(plug_cont local suffix)=gateway_cont_weight local+gateway_cont_weight suffix.
Proof. induction local;cbn;try rewrite IHlocal;lia. Qed.

Lemma gateway_continuation_plug source suffix :
  gateway_continuation(plug_state source suffix)=plug_cont(gateway_continuation source)suffix.
Proof. destruct source;reflexivity. Qed.

Lemma gateway_plug_cannot_shrink {World}(local:gateway_state World)suffix target target_world :
  gateway_cont_weight(gateway_continuation target)<gateway_cont_weight suffix ->
  gateway_plug local suffix<>gateway_live target target_world.
Proof.
  intros SMALL SAME;destruct local as[source world|memory world];cbn in SAME;try discriminate.
  inversion SAME;subst.
  rewrite gateway_continuation_plug,gateway_plug_cont_weight in SMALL;lia.
Qed.

(* §FS-host-boundary.caller: Reaching later caller code forces a return on this same wide run. *)
Theorem gateway_return_cut {World Event}(backend:gateway_backend World Event)ge
    definition arguments suffix before world events target target_world :
  is_call_cont suffix ->
  gateway_cont_weight(gateway_continuation target)<gateway_cont_weight suffix ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments suffix before)world)events
    (gateway_live target target_world) ->
  exists prefix rest returned memory returned_world,
    events=prefix++rest /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)prefix
      (gateway_live(Returnstate returned Kstop memory)returned_world) /\
    gateway_steps backend ge(gateway_live(Returnstate returned suffix memory)returned_world)rest
      (gateway_live target target_world).
Proof.
  intros CALL SMALL RUN.
  destruct(gateway_caller_run_decomposition backend ge suffix
    (Callstate definition arguments Kstop before)world events(gateway_live target target_world)CALL RUN)
    as[[local[LOCAL SAME]]|
      [prefix[rest[returned[memory[returned_world[EVENTS[LOCAL CONTINUE]]]]]]]].
  - exfalso;eapply gateway_plug_cannot_shrink;[exact SMALL|symmetry;exact SAME].
  - exists prefix,rest,returned,memory,returned_world;auto.
Qed.

Theorem gateway_callback_return_cut {World Event}(backend:gateway_backend World Event)ge
    definition arguments suffix before world events target_definition target_arguments
    target_cont after target_world :
  is_call_cont suffix ->gateway_cont_weight target_cont<gateway_cont_weight suffix ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments suffix before)world)events
    (gateway_live(Callstate target_definition target_arguments target_cont after)target_world) ->
  exists prefix rest returned memory returned_world,
    events=prefix++rest /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)prefix
      (gateway_live(Returnstate returned Kstop memory)returned_world) /\
    gateway_steps backend ge(gateway_live(Returnstate returned suffix memory)returned_world)rest
      (gateway_live(Callstate target_definition target_arguments target_cont after)target_world).
Proof. intros CALL SMALL RUN;eapply gateway_return_cut;eassumption. Qed.
