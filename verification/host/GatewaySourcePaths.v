(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual guarded source stores precede the selected call in the same run. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayFrames GatewaySourceCuts GatewayFramedRuntime.
Import ListNotations.

Inductive gateway_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    definition arguments continuation :
    (mem->World->Prop)->Clight.state->(mem->World->Prop)->Prop:=
|gateway_source_reached:forall property memory result,
    (forall memory world,property memory world->result memory world) ->
    gateway_source_path backend ge definition arguments continuation property
      (Callstate definition arguments continuation memory)result
|gateway_source_next:forall property source target middle result,
    gateway_ambient_closed backend property ->~gateway_at_primitive source ->
    (forall memory world,property memory world->exists changed,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory target changed) /\middle changed world) ->
    gateway_source_path backend ge definition arguments continuation middle target result ->
    gateway_source_path backend ge definition arguments continuation property source result.

Lemma gateway_source_same {World Event}(backend:gateway_backend World Event)ge
    definition arguments continuation property source target result :
  gateway_ambient_closed backend property ->~gateway_at_primitive source ->
  (forall memory world,property memory world->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory target memory)) ->
  gateway_source_path backend ge definition arguments continuation property target result ->
  gateway_source_path backend ge definition arguments continuation property source result.
Proof.
  intros CLOSED INTERNAL EDGE REST;eapply gateway_source_next;try eassumption.
  intros memory world GOOD;exists memory;split;[eapply EDGE;exact GOOD|exact GOOD].
Qed.

Theorem gateway_source_path_cut {World Event}(backend:gateway_backend World Event)ge
    definition arguments continuation property source result :
  gateway_source_path backend ge definition arguments continuation property source result ->
  forall before world events returned after next,property before world ->
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
      (gateway_live(Returnstate returned Kstop after)next) ->
    exists prefix suffix called_memory called_world,
      events=prefix++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
      gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)prefix
        (gateway_live(Callstate definition arguments continuation called_memory)called_world) /\
      result called_memory called_world /\
      gateway_steps backend ge(gateway_live(Callstate definition arguments continuation called_memory)called_world)suffix
        (gateway_live(Returnstate returned Kstop after)next).
Proof.
  intro SCRIPT;induction SCRIPT;intros before world events returned after next GOOD RUN.
  - exists[],events,before,world;cbn;split;[reflexivity|]. split;[constructor|].
    split;[constructor|]. split;[apply H;exact GOOD|exact RUN].
  - destruct(gateway_source_edge_cut backend ge property middle source target before world events returned after next
      H H0 H1 GOOD RUN)
      as(pending &rest &edge_before &current &edge_after &EVENTS &AMBIENT &PREFIX &EDGE_READY &EDGE &POST &REST).
    destruct(IHSCRIPT edge_after current rest returned after next POST REST)
      as(prefix &suffix &called_memory &called_world &TAIL &QUIET &TO_CALL &CALLED &SUFFIX).
    exists(pending++gateway_source E0::prefix),suffix,called_memory,called_world.
    split;[rewrite EVENTS,TAIL;rewrite<-app_assoc;reflexivity|].
    split.
    + apply Forall_app;split.
      * eapply Forall_impl;[|exact AMBIENT];intros event SAME;right;exact SAME.
      * constructor;[left;reflexivity|exact QUIET].
    + split.
      * eapply gateway_steps_append;[exact PREFIX|].
        destruct EDGE as[IN[REAL UNIQUE]].
        econstructor;[apply gateway_internal;[exact IN|exact REAL]|exact TO_CALL].
      * split;assumption.
Qed.
