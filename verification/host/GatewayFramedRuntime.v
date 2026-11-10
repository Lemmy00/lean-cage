(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Source certificates transport coupled memory/runtime facts per edge. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayFrames GatewayOperations GatewayPure.
Import ListNotations.

Definition gateway_ambient_closed {World Event}(backend:gateway_backend World Event)
    (property:mem->World->Prop) :Prop:=
  forall before world after next,property before world ->
    gateway_interference backend before world after next ->property after next.

(* Each certificate edge is an actual deterministic Clight edge. Runtime facts
   are transported by that edge, rather than by a whole-function premise. *)
Inductive gateway_runtime_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) :
    (mem->World->Prop)->Clight.state->val->(mem->World->Prop)->Prop:=
| gateway_runtime_return :forall property value memory result,
    gateway_ambient_closed backend property ->
    (forall memory world,property memory world->result memory world) ->
    gateway_runtime_path backend ge property(Returnstate value Kstop memory)value result
| gateway_runtime_next :forall property source next middle value result,
    gateway_ambient_closed backend property ->~gateway_at_primitive source ->
    (forall memory world,property memory world->exists after,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next after) /\
      middle after world) ->
    gateway_runtime_path backend ge middle next value result ->
    gateway_runtime_path backend ge property source value result.

Lemma gateway_runtime_same {World Event}(backend:gateway_backend World Event)ge
    property source next value result :
  gateway_ambient_closed backend property ->~gateway_at_primitive source ->
  (forall memory world,property memory world->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory next memory)) ->
  gateway_runtime_path backend ge property next value result ->
  gateway_runtime_path backend ge property source value result.
Proof.
  intros CLOSED INTERNAL EDGES REST.
  eapply gateway_runtime_next with(next:=next)(middle:=property).
  - exact CLOSED.
  - exact INTERNAL.
  - intros memory world GOOD;exists memory;split;[apply EDGES with(world:=world);exact GOOD|exact GOOD].
  - exact REST.
Qed.

Lemma gateway_runtime_replace {World Event}(backend:gateway_backend World Event)ge
    property source value result memory :
  gateway_runtime_path backend ge property source value result ->
  gateway_runtime_path backend ge property(gateway_replace_memory source memory)value result.
Proof.
  intro SCRIPT;induction SCRIPT;cbn.
  - constructor;assumption.
  - eapply gateway_runtime_next with(next:=gateway_replace_memory next memory)(middle:=middle).
    + exact H.
    + intro BAD;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))BAD).
    + intros changed world GOOD;rewrite gateway_memory_replace_twice.
      destruct(H1 changed world GOOD)as[after[EDGE NEXT]].
      exists after;rewrite gateway_memory_replace_twice;auto.
    + exact IHSCRIPT.
Qed.

Definition gateway_runtime_path_state {World Event}(backend:gateway_backend World Event)ge value result
    (state:gateway_state World) :Prop:=
  match state with
  |gateway_live source world=>exists property,
    property(memory_of source)world /\gateway_runtime_path backend ge property source value result
  |gateway_dead _ _=>True
  end.

Lemma gateway_runtime_path_step {World Event}(backend:gateway_backend World Event)ge
    before event after value result :
  gateway_runtime_path_state backend ge value result before ->gateway_step backend ge before event after ->
  gateway_runtime_path_state backend ge value result after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - destruct GOOD as[property[PROPERTY SCRIPT]];inversion SCRIPT;subst.
    + match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
    + match goal with EDGES:forall memory world,property memory world->_|-_=>
        destruct(EDGES(memory_of source)world PROPERTY)as[changed[[IN[REAL UNIQUE]]POST]]end.
      rewrite gateway_memory_replace_identity in UNIQUE.
      match goal with ACTUAL:step2 _ source _ _|-_=>
        destruct(UNIQUE _ _ ACTUAL)as[TRACE TARGET];subst end.
      exists middle;rewrite gateway_replace_memory_of;split;[exact POST|].
      apply gateway_runtime_replace;assumption.
  - destruct GOOD as[property[PROPERTY SCRIPT]];inversion SCRIPT;subst.
    match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end.
  - destruct GOOD as[property[PROPERTY SCRIPT]];inversion SCRIPT;subst.
    match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end.
  - destruct GOOD as[property[PROPERTY SCRIPT]];exists property;split.
    + rewrite gateway_replace_memory_of;inversion SCRIPT;subst;
        match goal with CLOSED:gateway_ambient_closed backend property|-_=>
          eapply CLOSED;eassumption end.
    + apply gateway_runtime_replace;exact SCRIPT.
  - destruct GOOD as[property[PROPERTY SCRIPT]];inversion SCRIPT;subst;contradiction.
Qed.

Theorem gateway_runtime_path_prefix {World Event}(backend:gateway_backend World Event)ge
    property source value result memory world events target :
  property memory world ->gateway_runtime_path backend ge property source value result ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source memory)world)events target ->
  gateway_runtime_path_state backend ge value result target.
Proof.
  intros PROPERTY SCRIPT RUN.
  assert(INITIAL:gateway_runtime_path_state backend ge value result
    (gateway_live(gateway_replace_memory source memory)world)).
  { exists property;rewrite gateway_replace_memory_of;split;[exact PROPERTY|].
    apply gateway_runtime_replace;exact SCRIPT. }
  revert INITIAL;induction RUN;intro GOOD;[exact GOOD|].
  apply IHRUN;eapply gateway_runtime_path_step;eassumption.
Qed.

(* §FS-host-boundary.caller: A successful wider run retains its exact memory and World. *)
Theorem gateway_runtime_path_return_exact {World Event}(backend:gateway_backend World Event)ge
    property source value result memory world events actual after next :
  property memory world ->gateway_runtime_path backend ge property source value result ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source memory)world)events
    (gateway_live(Returnstate actual Kstop after)next) ->
  actual=value /\result after next.
Proof.
  intros PROPERTY SCRIPT RUN.
  destruct(gateway_runtime_path_prefix backend ge property source value result memory world events _
    PROPERTY SCRIPT RUN)as[final_property[FINAL SCRIPT_FINAL]].
  inversion SCRIPT_FINAL;subst;[auto|].
  match goal with EDGES:forall memory world,final_property memory world->_|-_=>
    destruct(EDGES after next FINAL)as[changed[[_[REAL _]]POST]]end.
  cbn in REAL;inversion REAL.
Qed.

Theorem gateway_runtime_path_execution {World Event}(backend:gateway_backend World Event)ge
    property source value result :
  gateway_runtime_path backend ge property source value result ->
  forall memory world,property memory world ->exists events after,
    gateway_steps backend ge(gateway_live(gateway_replace_memory source memory)world)events
      (gateway_live(Returnstate value Kstop after)world) /\result after world.
Proof.
  intro SCRIPT;induction SCRIPT;intros initial world PROPERTY.
  - exists [],initial;split;[constructor|auto].
  - destruct(H1 initial world PROPERTY)as[changed[[INTERNAL[STEP UNIQUE]]MIDDLE]].
    destruct(IHSCRIPT changed world MIDDLE)as[events[after[REST POST]]].
    exists(gateway_source E0::events),after;split;[|exact POST].
    econstructor;[eapply gateway_internal;eassumption|exact REST].
Qed.
