(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual setup errors remain errors while successful paths retain their resources. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Integers Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayFrames
  GatewayFramedRuntime GatewayOperations GatewayIntegerFailures.
Import ListNotations.

Inductive gateway_setup_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (result:mem->World->Prop):(mem->World->Prop)->Clight.state->Prop:=
|gateway_setup_return:forall property memory,
    gateway_ambient_closed backend property->
    (forall memory world,property memory world->result memory world)->
    gateway_setup_path backend ge result property(Returnstate(Vint Int.zero)Kstop memory)
|gateway_setup_failure:forall property source,
    gateway_integer_failure_source source->gateway_setup_path backend ge result property source
|gateway_setup_next:forall property source next middle,
    gateway_ambient_closed backend property->~gateway_at_primitive source->
    (forall memory world,property memory world->exists after,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next after) /\middle after world)->
    gateway_setup_path backend ge result middle next->gateway_setup_path backend ge result property source
|gateway_setup_external:forall property external types result_type convention arguments continuation memory,
    gateway_ambient_closed backend property->
    (forall before world returned after next observed,
      property before world->gateway_external backend external types result_type convention arguments
        before world returned after next observed->
      exists middle,middle after next /\gateway_setup_path backend ge result middle
        (Returnstate returned continuation after))->
    gateway_setup_path backend ge result property
      (Callstate(External external types result_type convention)arguments continuation memory).

Lemma gateway_setup_same {World Event}(backend:gateway_backend World Event)ge result property source next:
  gateway_ambient_closed backend property->~gateway_at_primitive source->
  (forall memory world,property memory world->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory next memory))->
  gateway_setup_path backend ge result property next->gateway_setup_path backend ge result property source.
Proof.
  intros CLOSED INTERNAL EDGE REST;eapply gateway_setup_next with(next:=next)(middle:=property);
    [exact CLOSED|exact INTERNAL| |exact REST].
  intros memory world GOOD;exists memory;split;[apply EDGE with(world:=world);exact GOOD|exact GOOD].
Qed.

Lemma gateway_setup_failure_replace source memory:
  gateway_integer_failure_source source->gateway_integer_failure_source(gateway_replace_memory source memory).
Proof. destruct source;cbn;tauto. Qed.

Lemma gateway_setup_replace {World Event}(backend:gateway_backend World Event)ge result property source memory:
  gateway_setup_path backend ge result property source->
  gateway_setup_path backend ge result property(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;inversion SCRIPT;subst;cbn.
  - constructor;assumption.
  - apply gateway_setup_failure,gateway_setup_failure_replace;exact H.
  - eapply gateway_setup_next with(next:=next)(middle:=middle).
    + exact H.
    + intro BAD;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))BAD).
    + intros changed world GOOD;rewrite gateway_memory_replace_twice;apply H1;exact GOOD.
    + exact H2.
  - eapply gateway_setup_external;eassumption.
Qed.

Lemma gateway_setup_pre {World Event}(backend:gateway_backend World Event)ge result property source initial:
  gateway_setup_path backend ge result property source->gateway_ambient_closed backend initial->
  (forall memory world,initial memory world->property memory world)->
  gateway_setup_path backend ge result initial source.
Proof.
  intros SCRIPT CLOSED INCLUDED;inversion SCRIPT;subst.
  - constructor;[exact CLOSED|]. intros changed world GOOD;apply H0,INCLUDED;exact GOOD.
  - apply gateway_setup_failure;exact H.
  - eapply gateway_setup_next with(next:=next)(middle:=middle);[exact CLOSED|exact H0| |exact H2].
    intros memory world GOOD;apply H1,INCLUDED;exact GOOD.
  - eapply gateway_setup_external;[exact CLOSED|]. intros before world returned after next observed GOOD OPERATION.
    apply H0 with(before:=before)(world:=world)(observed:=observed);[apply INCLUDED;exact GOOD|exact OPERATION].
Qed.

Definition gateway_setup_state {World Event}(backend:gateway_backend World Event)ge result(state:gateway_state World):Prop:=
  match state with
  |gateway_live source world=>gateway_integer_failure_source source \/
    exists property,property(memory_of source)world /\gateway_setup_path backend ge result property source
  |gateway_dead _ _=>True end.

Lemma gateway_setup_step {World Event}(backend:gateway_backend World Event)ge before event after result:
  gateway_setup_state backend ge result before->gateway_step backend ge before event after->
  gateway_setup_state backend ge result after.
Proof.
  intros GOOD STEP.
  destruct before as[source world|memory world].
  - destruct GOOD as[FAILURE|[property[PROPERTY SCRIPT]]].
    + pose proof(gateway_integer_failure_step backend ge(gateway_live source world)event after FAILURE STEP)as FINAL.
      destruct after;cbn in *;tauto.
    + inversion STEP;subst;cbn in *;try exact I.
      * inversion SCRIPT;subst;try contradiction;
          try solve[match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end].
        -- match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
        -- left;eapply gateway_integer_failure_source_internal;eassumption.
        -- match goal with EDGES:forall memory world,property memory world->_|-_=>
            destruct(EDGES(memory_of source)world PROPERTY)as[changed[[IN[CANON UNIQUE]]POST]]end.
           rewrite gateway_memory_replace_identity in UNIQUE.
           match goal with REAL:step2 _ source _ _|-_=>destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst end.
           right;exists middle;rewrite gateway_replace_memory_of;split;[exact POST|apply gateway_setup_replace;assumption].
      * inversion SCRIPT;subst;try contradiction;
          try solve[match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end].
        -- left;left;exact H.
        -- match goal with POST:forall before world returned after next observed,?current before world->_|-_=>
            destruct(POST _ _ _ _ _ _ PROPERTY ltac:(eassumption))as[middle[READY REST]]end.
           right;exists middle;split;assumption.
      * inversion SCRIPT;subst;try contradiction;
          try solve[match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end].
        left;exact H.
      * inversion SCRIPT;subst.
        -- right;exists property;split.
           ++ rewrite gateway_replace_memory_of;eapply H;eassumption.
           ++ apply gateway_setup_replace;exact SCRIPT.
        -- left;apply gateway_setup_failure_replace;exact H.
        -- right;exists property;split.
           ++ rewrite gateway_replace_memory_of;eapply H;eassumption.
           ++ apply gateway_setup_replace;exact SCRIPT.
        -- right;exists property;split.
           ++ rewrite gateway_replace_memory_of;eapply H;eassumption.
           ++ apply gateway_setup_replace;exact SCRIPT.
      * right;exists property;split;assumption.
  - inversion STEP;subst;exact I.
Qed.

Theorem gateway_setup_return_exact {World Event}(backend:gateway_backend World Event)ge result property source
    before world events after next:
  property before world->gateway_setup_path backend ge result property source->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->result after next.
Proof.
  intros PROPERTY SCRIPT RUN.
  assert(INITIAL:gateway_setup_state backend ge result(gateway_live(gateway_replace_memory source before)world)).
  { right;exists property;rewrite gateway_replace_memory_of;split;[exact PROPERTY|apply gateway_setup_replace;exact SCRIPT]. }
  assert(FINAL:gateway_setup_state backend ge result(gateway_live(Returnstate(Vint Int.zero)Kstop after)next)).
  { revert INITIAL;induction RUN;intro GOOD;[exact GOOD|apply IHRUN;eapply gateway_setup_step;eassumption]. }
  destruct FINAL as[FAILURE|[final_property[READY REST]]].
  - cbn[gateway_integer_failure_source gateway_nested_integer_failure]in FAILURE;destruct FAILURE as[FALSE|[_ BAD]];
      [contradiction|discriminate BAD].
  - inversion REST;subst;[apply H2;exact READY| |].
    + cbn[gateway_integer_failure_source gateway_nested_integer_failure]in H;destruct H as[FALSE|[_ BAD]];
        [contradiction|discriminate BAD].
    + match goal with EDGES:forall memory world,final_property memory world->_|-_=>
        destruct(EDGES after next READY)as[changed[[_[REAL _]]POST]]end;cbn in REAL;inversion REAL.
Qed.
