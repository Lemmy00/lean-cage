(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A source failure guard excludes later allocation on every actual prefix. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayFrames GatewayCallPath
  GatewayFramedRuntime GatewayFailurePaths.
Import ListNotations.

Inductive gateway_failure_control {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) :
    (Memory.mem->World->Prop)->Clight.state->Prop:=
|gateway_failure_control_selected:forall property source,gateway_null_source source ->
    gateway_failure_control backend ge property source
|gateway_failure_control_next:forall property source target middle,
    gateway_ambient_closed backend property ->~gateway_at_primitive source ->
    (forall memory world,property memory world ->exists changed,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory target changed) /\middle changed world) ->
    gateway_failure_control backend ge middle target ->gateway_failure_control backend ge property source.

Lemma gateway_failure_control_same {World Event}(backend:gateway_backend World Event)ge property source target :
  gateway_ambient_closed backend property ->~gateway_at_primitive source ->
  (forall memory world,property memory world ->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory target memory)) ->
  gateway_failure_control backend ge property target ->gateway_failure_control backend ge property source.
Proof.
  intros CLOSED INTERNAL EDGE REST;eapply gateway_failure_control_next;try eassumption.
  intros memory world GOOD;exists memory;split;[exact(EDGE memory world GOOD)|exact GOOD].
Qed.

Lemma gateway_null_source_replace source memory :
  gateway_null_source source ->gateway_null_source(gateway_replace_memory source memory).
Proof. destruct source;exact(fun H=>H). Qed.

Lemma gateway_failure_control_replace {World Event}(backend:gateway_backend World Event)ge property source memory :
  gateway_failure_control backend ge property source ->
  gateway_failure_control backend ge property(gateway_replace_memory source memory).
Proof.
  intro CONTROL;induction CONTROL.
  - constructor;apply gateway_null_source_replace;exact H.
  - eapply gateway_failure_control_next with(target:=gateway_replace_memory target memory)(middle:=middle).
    + exact H.
    + intro PRIMITIVE;apply H0;apply(proj1(gateway_memory_replace_primitive source memory));exact PRIMITIVE.
    + intros current world GOOD;rewrite gateway_memory_replace_twice.
      destruct(H1 current world GOOD)as[changed[EDGE AFTER]].
      exists changed;rewrite gateway_memory_replace_twice;split;assumption.
    + exact IHCONTROL.
Qed.

Definition gateway_failure_control_state {World Event}(backend:gateway_backend World Event)ge(state:gateway_state World):Prop:=
  match state with
  |gateway_live source world=>gateway_null_source source \/exists property,
    property(memory_of source)world /\gateway_failure_control backend ge property source
  |gateway_dead _ _=>True
  end.

Lemma gateway_failure_control_step {World Event}(backend:gateway_backend World Event)ge before observed after :
  gateway_failure_control_state backend ge before ->gateway_step backend ge before observed after ->
  gateway_failure_control_state backend ge after.
Proof.
  intros GOOD STEP;destruct before as[source world|memory world];[|inversion STEP].
  destruct GOOD as[NULL|[property[READY CONTROL]]].
  - pose proof(gateway_null_step backend ge(gateway_live source world)observed after NULL STEP)as NEXT;
      destruct after;[left;exact NEXT|exact I].
  - inversion CONTROL;subst.
    + pose proof(gateway_null_step backend ge(gateway_live source world)observed after H STEP)as NEXT;
        destruct after;[left;exact NEXT|exact I].
    + destruct(gateway_nonprimitive_step backend ge _ _ _ _ H0 STEP)
        as[[trace[following[EVENT[REAL TARGET]]]]|
          [[changed[next[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
      * destruct(H1(memory_of source)world READY)as[changed[EDGE AFTER]].
        destruct EDGE as[INTERNAL[CANON UNIQUE]];rewrite gateway_memory_replace_identity in CANON,UNIQUE.
        destruct(UNIQUE _ _ REAL)as[ZERO SAME];subst.
        right;exists middle;rewrite gateway_replace_memory_of;split;[exact AFTER|].
        apply gateway_failure_control_replace;exact H2.
      * right;exists property;rewrite gateway_replace_memory_of;split.
        -- eapply H;[exact READY|exact INTERFERENCE].
        -- apply gateway_failure_control_replace;exact CONTROL.
      * exact I.
Qed.

Theorem gateway_failure_control_prefix {World Event}(backend:gateway_backend World Event)ge property source before world events target :
  gateway_failure_control backend ge property source ->property before world ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events target ->
  gateway_failure_control_state backend ge target.
Proof.
  intros CONTROL READY RUN.
  assert(INITIAL:gateway_failure_control_state backend ge(gateway_live(gateway_replace_memory source before)world)).
  { right;exists property;rewrite gateway_replace_memory_of;split;[exact READY|].
    apply gateway_failure_control_replace;exact CONTROL. }
  revert INITIAL;induction RUN;intro GOOD;[exact GOOD|].
  apply IHRUN;eapply gateway_failure_control_step;eassumption.
Qed.

Theorem gateway_failure_control_cannot_call {World Event}(backend:gateway_backend World Event)ge property source
    before world events external types result_type convention arguments continuation memory next :
  gateway_failure_control backend ge property source ->property before world ->~gateway_nested_null continuation ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Callstate(External external types result_type convention)arguments continuation memory)next) ->False.
Proof.
  intros CONTROL READY NOT_NULL RUN.
  destruct(gateway_failure_control_prefix backend ge property source before world events _ CONTROL READY RUN)
    as[NULL|[current[GOOD PLAN]]].
  - exact(NOT_NULL NULL).
  - inversion PLAN;subst;[exact(NOT_NULL H)|apply H0;exact I].
Qed.
