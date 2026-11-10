(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Each source edge preserves its actual coupled state and event position. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayFrames GatewayOperations GatewayPure GatewayCallPath
  GatewayContexts GatewayFailurePaths GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_source_edge_cut {World Event}(backend:gateway_backend World Event)ge
    (property middle:mem->World->Prop)source target before world events returned after next :
  gateway_ambient_closed backend property ->~gateway_at_primitive source ->
  (forall memory current,property memory current->exists changed,
    store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory target changed) /\
    middle changed current) ->
  property before world ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  exists pending rest edge_before current edge_after,
    events=pending++gateway_source E0::rest /\
    Forall(fun event=>event=gateway_ambient)pending /\
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)pending
      (gateway_live(gateway_replace_memory source edge_before)current) /\
    property edge_before current /\
    store_edge ge(gateway_replace_memory source edge_before)(gateway_replace_memory target edge_after) /\
    middle edge_after current /\
    gateway_steps backend ge(gateway_live(gateway_replace_memory target edge_after)current)rest
      (gateway_live(Returnstate returned Kstop after)next).
Proof.
  intros CLOSED INTERNAL EDGES;revert before world.
  induction events as[|event rest IH];intros before world GOOD RUN.
  - inversion RUN;subst.
    destruct(EDGES before next GOOD)as[changed[[_[REAL _]]POST]].
    match goal with SAME:gateway_replace_memory source before=Returnstate _ _ _|-_=>
      rewrite SAME in REAL;inversion REAL end.
  - inversion RUN as[|first observed following remaining last HEAD TAIL];subst.
    assert(NONPRIMITIVE:~gateway_at_primitive(gateway_replace_memory source before)).
    { intro BAD;apply INTERNAL;exact((proj1(gateway_memory_replace_primitive source before))BAD). }
    destruct(gateway_nonprimitive_step backend ge _ _ _ _ NONPRIMITIVE HEAD)
      as[[trace[actual[EVENT[REAL TARGET]]]]|
        [[changed[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + destruct(EDGES before world GOOD)as[changed[EDGE POST]].
      destruct EDGE as[IN[CANON UNIQUE]].
      destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst.
      exists[],rest,before,world,changed;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|].
      split;[exact GOOD|]. split;[split;[exact IN|split;assumption]|]. split;assumption.
    + rewrite gateway_replace_memory_of in INTERFERENCE.
      rewrite gateway_memory_replace_twice in TAIL.
      destruct(IH changed current(CLOSED _ _ _ _ GOOD INTERFERENCE)TAIL)
        as(pending &suffix &edge_before &edge_world &edge_after &EVENTS &AMBIENT &PREFIX &
          EDGE_READY &EDGE &POST &REST).
      exists(gateway_ambient::pending),suffix,edge_before,edge_world,edge_after.
      split;[cbn;congruence|]. split;[constructor;[reflexivity|exact AMBIENT]|]. split.
      * econstructor;[apply gateway_interleaved;rewrite gateway_replace_memory_of;exact INTERFERENCE|].
        rewrite gateway_memory_replace_twice;exact PREFIX.
      * split;[exact EDGE_READY|]. split;[exact EDGE|]. split;assumption.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

Definition gateway_failure_when {World Event}(backend:gateway_backend World Event)ge
    (property:mem->World->Prop)source :Prop:=
  forall before world events value after next,property before world->
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
      (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.

Lemma gateway_failure_when_selected {World Event}(backend:gateway_backend World Event)ge
    property source :gateway_failure_result backend ge source->gateway_failure_when backend ge property source.
Proof. intros FAILURE before world events value after next GOOD RUN;eapply FAILURE;exact RUN. Qed.

Lemma gateway_failure_when_edge {World Event}(backend:gateway_backend World Event)ge
    property middle source target :
  gateway_ambient_closed backend property ->~gateway_at_primitive source ->
  (forall memory world,property memory world->exists changed,
    store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory target changed) /\middle changed world) ->
  gateway_failure_when backend ge middle target ->gateway_failure_when backend ge property source.
Proof.
  intros CLOSED INTERNAL EDGES FAILURE before world events value after next GOOD RUN.
  destruct(gateway_source_edge_cut backend ge property middle source target before world events value after next
    CLOSED INTERNAL EDGES GOOD RUN)
    as(prefix &suffix &edge_before &current &edge_after &EVENTS &AMBIENT &PREFIX &
      EDGE_READY &EDGE &POST &REST).
  eapply FAILURE;[exact POST|exact REST].
Qed.

Lemma gateway_failure_when_same {World Event}(backend:gateway_backend World Event)ge
    property source target :
  gateway_ambient_closed backend property ->~gateway_at_primitive source ->
  (forall memory world,property memory world->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory target memory)) ->
  gateway_failure_when backend ge property target ->gateway_failure_when backend ge property source.
Proof.
  intros CLOSED INTERNAL EDGES REST;eapply gateway_failure_when_edge;try eassumption.
  intros memory world GOOD;exists memory;split;[eapply EDGES;exact GOOD|exact GOOD].
Qed.
