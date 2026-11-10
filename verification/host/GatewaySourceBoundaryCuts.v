(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source phase cuts hold before a pending external call. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayFrames GatewayOperations GatewayPure GatewayCallPath
  GatewayFramedRuntime GatewaySourceSegments GatewaySourcePaths.
Import ListNotations.

Theorem gateway_source_edge_external_cut {World Event}(backend:gateway_backend World Event)ge
    (property middle:mem->World->Prop)source target before world events external types result_type convention arguments continuation after next :
  gateway_ambient_closed backend property ->~gateway_at_primitive source ->
  (forall memory current,property memory current->exists changed,
    store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory target changed) /\
    middle changed current) ->
  property before world ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Callstate (External external types result_type convention) arguments continuation after)next) ->
  exists pending rest edge_before current edge_after,
    events=pending++gateway_source E0::rest /\
    Forall(fun event=>event=gateway_ambient)pending /\
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)pending
      (gateway_live(gateway_replace_memory source edge_before)current) /\
    property edge_before current /\
    store_edge ge(gateway_replace_memory source edge_before)(gateway_replace_memory target edge_after) /\
    middle edge_after current /\
    gateway_steps backend ge(gateway_live(gateway_replace_memory target edge_after)current)rest
      (gateway_live(Callstate (External external types result_type convention) arguments continuation after)next).
Proof.
  intros CLOSED INTERNAL EDGES;revert before world.
  induction events as[|event rest IH];intros before world GOOD RUN.
  - inversion RUN; subst.
    match goal with SAME : gateway_replace_memory source _ = Callstate _ _ _ _ |- _ =>
      exfalso; apply INTERNAL; apply (proj1 (gateway_memory_replace_primitive source before)); rewrite SAME; exact I end.
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

Theorem gateway_source_segment_external_cut {World Event}(backend:gateway_backend World Event)ge
    property source target result :gateway_source_segment backend ge property source target result ->
  forall before world events external types result_type convention arguments continuation after next,property before world ->
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
      (gateway_live(Callstate (External external types result_type convention) arguments continuation after)next) ->
    exists prefix suffix memory current,
      events=prefix++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
      gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)prefix
        (gateway_live(gateway_replace_memory target memory)current) /\result memory current /\
      gateway_steps backend ge(gateway_live(gateway_replace_memory target memory)current)suffix
        (gateway_live(Callstate (External external types result_type convention) arguments continuation after)next).
Proof.
  intro SEGMENT;induction SEGMENT;intros before world events external types result_type convention arguments continuation after final_world GOOD RUN.
  - exists[],events,before,world;cbn;split;[reflexivity|]. split;[constructor|].
    split;[constructor|]. split;assumption.
  - destruct(gateway_source_edge_external_cut backend ge property middle source next before world events external types result_type convention arguments continuation after final_world
      H H0 H1 GOOD RUN)
      as(pending &rest &edge_before &edge_world &edge_after &EVENTS &AMBIENT &PREFIX &EDGE_READY &EDGE &POST &REST).
    destruct(IHSEGMENT edge_after edge_world rest external types result_type convention arguments continuation after final_world POST REST)
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
