(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Guarded source phases compose at the same memory and runtime frontier. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayFrames GatewayFramedRuntime
  GatewaySourceCuts GatewaySourcePaths.
Import ListNotations.

Inductive gateway_source_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) :
    (mem->World->Prop)->Clight.state->Clight.state->(mem->World->Prop)->Prop:=
|gateway_segment_here:forall property source,gateway_source_segment backend ge property source source property
|gateway_segment_next:forall property source next middle target result,
    gateway_ambient_closed backend property ->~gateway_at_primitive source ->
    (forall memory world,property memory world->exists changed,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next changed) /\middle changed world) ->
    gateway_source_segment backend ge middle next target result ->
    gateway_source_segment backend ge property source target result.

Lemma gateway_segment_same {World Event}(backend:gateway_backend World Event)ge
    property source next target result :
  gateway_ambient_closed backend property ->~gateway_at_primitive source ->
  (forall memory world,property memory world->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory next memory)) ->
  gateway_source_segment backend ge property next target result ->
  gateway_source_segment backend ge property source target result.
Proof.
  intros CLOSED INTERNAL EDGES REST;eapply gateway_segment_next;try eassumption.
  intros memory world GOOD;exists memory;split;[eapply EDGES;exact GOOD|exact GOOD].
Qed.

Theorem gateway_segment_then_call {World Event}(backend:gateway_backend World Event)ge
    property source target middle definition arguments continuation result :
  gateway_source_segment backend ge property source target middle ->
  gateway_source_path backend ge definition arguments continuation middle target result ->
  gateway_source_path backend ge definition arguments continuation property source result.
Proof.
  intros SEGMENT;induction SEGMENT;intro REST;[exact REST|].
  eapply gateway_source_next;[exact H|exact H0|exact H1|apply IHSEGMENT;exact REST].
Qed.

Theorem gateway_source_segment_cut {World Event}(backend:gateway_backend World Event)ge
    property source target result :gateway_source_segment backend ge property source target result ->
  forall before world events value after next,property before world ->
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
      (gateway_live(Returnstate value Kstop after)next) ->
    exists prefix suffix memory current,
      events=prefix++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
      gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)prefix
        (gateway_live(gateway_replace_memory target memory)current) /\result memory current /\
      gateway_steps backend ge(gateway_live(gateway_replace_memory target memory)current)suffix
        (gateway_live(Returnstate value Kstop after)next).
Proof.
  intro SEGMENT;induction SEGMENT;intros before world events value after final_world GOOD RUN.
  - exists[],events,before,world;cbn;split;[reflexivity|]. split;[constructor|].
    split;[constructor|]. split;assumption.
  - destruct(gateway_source_edge_cut backend ge property middle source next before world events value after final_world
      H H0 H1 GOOD RUN)
      as(pending &rest &edge_before &edge_world &edge_after &EVENTS &AMBIENT &PREFIX &EDGE_READY &EDGE &POST &REST).
    destruct(IHSEGMENT edge_after edge_world rest value after final_world POST REST)
      as(prefix &suffix &memory &current &TAIL &QUIET &TO_TARGET &RESULT &SUFFIX).
    exists(pending++gateway_source E0::prefix),suffix,memory,current.
    split;[rewrite EVENTS,TAIL;rewrite<-app_assoc;reflexivity|]. split.
    + apply Forall_app;split.
      * eapply Forall_impl;[|exact AMBIENT];intros event SAME;right;exact SAME.
      * constructor;[left;reflexivity|exact QUIET].
    + split.
      * eapply gateway_steps_append;[exact PREFIX|]. destruct EDGE as[IN[REAL UNIQUE]].
        econstructor;[apply gateway_internal;[exact IN|exact REAL]|exact TO_TARGET].
      * split;assumption.
Qed.
