(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Source scripts cross individual effects in the same run. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayCallPath GatewayFrames
  GatewayFramedRuntime GatewayOperations.
Import ListNotations.

Inductive gateway_effect_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv):
    (mem->World->Prop)->Clight.state->val->(mem->World->Prop)->Prop:=
|gateway_effect_return:forall property value memory result,
    gateway_ambient_closed backend property->
    (forall memory world,property memory world->result memory world)->
    gateway_effect_path backend ge property(Returnstate value Kstop memory)value result
|gateway_effect_next:forall property source next middle value result,
    gateway_ambient_closed backend property->~gateway_at_primitive source->
    (forall memory world,property memory world->exists after,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next after) /\middle after world)->
    gateway_effect_path backend ge middle next value result->
    gateway_effect_path backend ge property source value result
|gateway_effect_external:forall property external types result_type convention arguments continuation memory value result,
    gateway_ambient_closed backend property->
    (forall before world returned after next observed,
      property before world->gateway_external backend external types result_type convention arguments
        before world returned after next observed->
      exists middle,middle after next /\gateway_effect_path backend ge middle
        (Returnstate returned continuation after)value result)->
    gateway_effect_path backend ge property
      (Callstate(External external types result_type convention)arguments continuation memory)value result.

Lemma gateway_effect_same {World Event}(backend:gateway_backend World Event)ge property source next value result:
  gateway_ambient_closed backend property->~gateway_at_primitive source->
  (forall memory world,property memory world->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory next memory))->
  gateway_effect_path backend ge property next value result->
  gateway_effect_path backend ge property source value result.
Proof.
  intros CLOSED INTERNAL EDGE REST;eapply gateway_effect_next with(next:=next)(middle:=property);
    [exact CLOSED|exact INTERNAL| |exact REST].
  intros memory world GOOD;exists memory;split;[apply EDGE with(world:=world);exact GOOD|exact GOOD].
Qed.

Lemma gateway_effect_replace {World Event}(backend:gateway_backend World Event)ge property source value result memory:
  gateway_effect_path backend ge property source value result->
  gateway_effect_path backend ge property(gateway_replace_memory source memory)value result.
Proof.
  intro SCRIPT;inversion SCRIPT;subst;cbn.
  - constructor;assumption.
  - eapply gateway_effect_next with(next:=next)(middle:=middle).
    + exact H.
    + intro BAD;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))BAD).
    + intros changed world GOOD;rewrite gateway_memory_replace_twice;apply H1;exact GOOD.
    + exact H2.
  - eapply gateway_effect_external;eassumption.
Qed.

Lemma gateway_effect_pre {World Event}(backend:gateway_backend World Event)ge property source value result initial:
  gateway_effect_path backend ge property source value result->gateway_ambient_closed backend initial->
  (forall memory world,initial memory world->property memory world)->
  gateway_effect_path backend ge initial source value result.
Proof.
  intros SCRIPT CLOSED INCLUDED;inversion SCRIPT;subst.
  - constructor;[exact CLOSED|]. intros available current GOOD;apply H0;apply INCLUDED;exact GOOD.
  - eapply gateway_effect_next with(next:=next)(middle:=middle);[exact CLOSED|exact H0| |exact H2].
    intros available current GOOD;apply H1;apply INCLUDED;exact GOOD.
  - eapply gateway_effect_external;[exact CLOSED|]. intros before world returned after next observed GOOD OPERATION.
    apply H0 with(before:=before)(world:=world)(observed:=observed);[apply INCLUDED;exact GOOD|exact OPERATION].
Qed.

Definition gateway_effect_state {World Event}(backend:gateway_backend World Event)ge value result(state:gateway_state World):Prop:=
  match state with
  |gateway_live source world=>exists property,property(memory_of source)world /\
    gateway_effect_path backend ge property source value result
  |gateway_dead _ _=>True end.

Lemma gateway_effect_step {World Event}(backend:gateway_backend World Event)ge before event after value result:
  gateway_effect_state backend ge value result before->gateway_step backend ge before event after->
  gateway_effect_state backend ge value result after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - destruct GOOD as[property[PROPERTY SCRIPT]];inversion SCRIPT;subst;try contradiction.
    all:try solve[match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end].
    + match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
    + match goal with EDGES:forall memory world,property memory world->_|-_=>
        destruct(EDGES(memory_of source)world PROPERTY)as[changed[[IN[CANON UNIQUE]]POST]]end.
      rewrite gateway_memory_replace_identity in UNIQUE.
      match goal with REAL:step2 _ source _ _|-_=>destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst end.
      exists middle;rewrite gateway_replace_memory_of;split;[exact POST|apply gateway_effect_replace;assumption].
  - destruct GOOD as[property[PROPERTY SCRIPT]];inversion SCRIPT;subst;try contradiction.
    all:try solve[match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end].
    match goal with POST:forall before world returned after next observed,property before world->_|-_=>
      destruct(POST _ _ _ _ _ _ PROPERTY ltac:(eassumption))as[middle[READY REST]]end.
    exists middle;split;assumption.
  - destruct GOOD as[property[PROPERTY SCRIPT]];inversion SCRIPT;subst.
    match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end.
  - destruct GOOD as[property[PROPERTY SCRIPT]];exists property;split.
    + rewrite gateway_replace_memory_of;inversion SCRIPT;subst;
        match goal with CLOSED:gateway_ambient_closed backend property|-_=>eapply CLOSED;eassumption end.
    + apply gateway_effect_replace;exact SCRIPT.
  - destruct GOOD as[property[PROPERTY SCRIPT]];exists property;split;assumption.
Qed.

Theorem gateway_effect_prefix {World Event}(backend:gateway_backend World Event)ge property source value result before world events target:
  property before world->gateway_effect_path backend ge property source value result->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events target->
  gateway_effect_state backend ge value result target.
Proof.
  intros PROPERTY SCRIPT RUN.
  assert(INITIAL:gateway_effect_state backend ge value result(gateway_live(gateway_replace_memory source before)world)).
  { exists property;rewrite gateway_replace_memory_of;split;[exact PROPERTY|apply gateway_effect_replace;exact SCRIPT]. }
  revert INITIAL;induction RUN;intro GOOD;[exact GOOD|]. apply IHRUN;eapply gateway_effect_step;eassumption.
Qed.

Theorem gateway_effect_return_exact {World Event}(backend:gateway_backend World Event)ge property source value result
    before world events actual after next:
  property before world->gateway_effect_path backend ge property source value result->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Returnstate actual Kstop after)next)->actual=value /\result after next.
Proof.
  intros PROPERTY SCRIPT RUN.
  destruct(gateway_effect_prefix backend ge property source value result before world events _ PROPERTY SCRIPT RUN)
    as[final_property[FINAL REST]].
  inversion REST;subst;[auto|].
  match goal with EDGES:forall memory world,final_property memory world->_|-_=>
    destruct(EDGES after next FINAL)as[changed[[_[REAL _]]POST]]end.
  cbn in REAL;inversion REAL.
Qed.
