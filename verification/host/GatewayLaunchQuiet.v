(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The same selected launch prefix retains all quiet source steps. *)
From Stdlib Require Import List Lia Wf_nat.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFrames GatewayPure
  GatewayOperations GatewayFramedRuntime GatewaySpawnABI GatewayReturnBarrier GatewayLaunchPaths GatewayReadonly GatewayCallPath.
Import ListNotations.

Inductive gateway_quiet_launch_path {World Event}(backend:gateway_backend World Event)
    (target:Clight.state->World->Prop):(mem->World->Prop)->Clight.state->Prop:=
|gateway_quiet_launch_reached:forall property source,
    (forall memory world,property memory world->target(gateway_replace_memory source memory)world)->
    gateway_quiet_launch_path backend target property source
|gateway_quiet_launch_failure:forall property owner environment allowed body continuation temporaries memory,
    gateway_barrier_bindings(Clight.globalenv prog)environment allowed(gateway_spawn_signature gateway_posix_spawn_api)->
    gateway_barrier_returns allowed body->call_cont continuation=Kstop->
    gateway_quiet_launch_path backend target property(State owner body continuation environment temporaries memory)
|gateway_quiet_launch_stuck:forall property source,
    gateway_ambient_closed backend property->~gateway_at_primitive source->gateway_launch_not_spawn source->
    (forall memory world trace after,property memory world->
      ~step2(Clight.globalenv prog)(gateway_replace_memory source memory)trace after)->
    gateway_quiet_launch_path backend target property source
|gateway_quiet_launch_next:forall property source following middle,
    gateway_ambient_closed backend property->~gateway_at_primitive source->gateway_launch_not_spawn source->
    (forall memory world,property memory world->exists after,
      store_edge(Clight.globalenv prog)(gateway_replace_memory source memory)(gateway_replace_memory following after) /\
      middle after world)->
    gateway_quiet_launch_path backend target middle following->
    gateway_quiet_launch_path backend target property source.

Lemma gateway_quiet_launch_replace {World Event}(backend:gateway_backend World Event)target property source memory:
  gateway_quiet_launch_path backend target property source->
  gateway_quiet_launch_path backend target property(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;inversion SCRIPT;subst;cbn.
  - eapply gateway_quiet_launch_reached;intros before world READY.
    rewrite gateway_memory_replace_twice;apply H;exact READY.
  - eapply gateway_quiet_launch_failure;eassumption.
  - eapply gateway_quiet_launch_stuck.
    + exact H.
    + intro BAD;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))BAD).
    + apply gateway_launch_not_spawn_replace;exact H1.
    + intros before world trace after READY;rewrite gateway_memory_replace_twice;apply H2 with(world:=world);exact READY.
  - eapply gateway_quiet_launch_next with(following:=following)(middle:=middle).
    + exact H.
    + intro BAD;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))BAD).
    + apply gateway_launch_not_spawn_replace;exact H1.
    + intros before world READY;rewrite gateway_memory_replace_twice;apply H2;exact READY.
    + exact H3.
Qed.

Lemma gateway_quiet_launch_same {World Event}(backend:gateway_backend World Event)target property source following:
  gateway_ambient_closed backend property->~gateway_at_primitive source->gateway_launch_not_spawn source->
  (forall memory world,property memory world->
    store_edge(Clight.globalenv prog)(gateway_replace_memory source memory)(gateway_replace_memory following memory))->
  gateway_quiet_launch_path backend target property following->
  gateway_quiet_launch_path backend target property source.
Proof.
  intros CLOSED INTERNAL DIFFERENT EDGE REST.
  eapply gateway_quiet_launch_next with(following:=following)(middle:=property);
    [exact CLOSED|exact INTERNAL|exact DIFFERENT| |exact REST].
  intros memory world READY;exists memory;split;[apply EDGE with(world:=world);exact READY|exact READY].
Qed.

Theorem gateway_quiet_launch_cut {World Event}(backend:gateway_backend World Event)target property source
    before world events arguments continuation after next:
  gateway_quiet_launch_path backend target property source->property before world->
  gateway_steps backend(Clight.globalenv prog)(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists prefix suffix selected current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend(Clight.globalenv prog)(gateway_live(gateway_replace_memory source before)world)prefix
      (gateway_live selected current) /\target selected current /\
    gateway_steps backend(Clight.globalenv prog)(gateway_live selected current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  remember(length events)as size eqn:SIZE;revert events SIZE property source before world.
  induction size using lt_wf_ind;intros events SIZE property source before world SCRIPT READY RUN.
  inversion SCRIPT as[reached_property reached_source MATCH|
    failed_property owner environment allowed body failed_cont temporaries template BINDINGS RETURNS STOP|
    stuck_property code CLOSED INTERNAL NOT_SPAWN STUCK|
    step_property code following middle CLOSED INTERNAL NOT_SPAWN EDGES REST];subst.
  - exists[],events,(gateway_replace_memory source before),world;cbn.
    split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;[apply MATCH;exact READY|exact RUN].
  - exfalso;eapply gateway_return_barrier_excludes_call;[exact BINDINGS|exact RETURNS|exact STOP|exact RUN].
  - destruct events as[|event rest].
    + inversion RUN;subst;exfalso.
      pose proof(gateway_launch_not_spawn_replace source before NOT_SPAWN)as NOT.
      match goal with SAME:gateway_replace_memory source before=Callstate _ _ _ _|-_=>rewrite SAME in NOT end.
      exact(NOT eq_refl).
    + inversion RUN as[|first observed actual_middle remaining last STEP TAIL];subst.
      destruct(gateway_nonprimitive_step backend(Clight.globalenv prog)_ _ _ _
        ltac:(intro BAD;apply INTERNAL;exact((proj1(gateway_memory_replace_primitive source before))BAD))STEP)
        as[[trace[actual[EVENT[REAL TARGET]]]]|
          [[changed[later[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
      * exfalso;exact(STUCK before world trace actual READY REAL).
      * assert(PROPERTY:property changed later).
        { eapply CLOSED;[exact READY|]. rewrite gateway_replace_memory_of in INTERFERENCE;exact INTERFERENCE. }
        rewrite gateway_memory_replace_twice in TAIL.
        destruct(H(length rest)ltac:(cbn;lia)rest eq_refl property(gateway_replace_memory source changed)
          changed later(gateway_quiet_launch_replace _ _ _ _ _ SCRIPT)PROPERTY
          ltac:(rewrite gateway_memory_replace_twice;exact TAIL))
          as(prefix&suffix&selected&current&EVENTS&QUIET&PREFIX&FINAL&SUFFIX).
        exists(gateway_ambient::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split;[constructor;[right;reflexivity|exact QUIET]|]. split.
        -- econstructor;[apply gateway_interleaved;exact INTERFERENCE|].
           rewrite gateway_memory_replace_twice in PREFIX|-*;exact PREFIX.
        -- split;assumption.
      * destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
  - destruct events as[|event rest].
    + inversion RUN;subst;exfalso.
      pose proof(gateway_launch_not_spawn_replace source before NOT_SPAWN)as NOT.
      match goal with SAME:gateway_replace_memory source before=Callstate _ _ _ _|-_=>rewrite SAME in NOT end.
      exact(NOT eq_refl).
    + inversion RUN as[|first observed actual_middle remaining last STEP TAIL];subst.
      destruct(gateway_nonprimitive_step backend(Clight.globalenv prog)_ _ _ _
        ltac:(intro BAD;apply INTERNAL;exact((proj1(gateway_memory_replace_primitive source before))BAD))STEP)
        as[[trace[actual[EVENT[REAL TARGET]]]]|
          [[changed[later[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
      * destruct(EDGES before world READY)as[changed[[INTERNAL_SOURCE[CANON UNIQUE]]POST]].
        destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst trace actual.
        destruct(H(length rest)ltac:(cbn;lia)rest eq_refl middle following changed world REST POST TAIL)
          as(prefix&suffix&selected&current&EVENTS&QUIET&PREFIX&FINAL&SUFFIX).
        exists(gateway_source E0::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split;[constructor;[left;reflexivity|exact QUIET]|]. split.
        -- econstructor;[apply gateway_internal;[exact INTERNAL_SOURCE|exact CANON]|exact PREFIX].
        -- split;assumption.
      * assert(PROPERTY:property changed later).
        { eapply CLOSED;[exact READY|]. rewrite gateway_replace_memory_of in INTERFERENCE;exact INTERFERENCE. }
        rewrite gateway_memory_replace_twice in TAIL.
        destruct(H(length rest)ltac:(cbn;lia)rest eq_refl property(gateway_replace_memory source changed)
          changed later(gateway_quiet_launch_replace _ _ _ _ _ SCRIPT)PROPERTY
          ltac:(rewrite gateway_memory_replace_twice;exact TAIL))
          as(prefix&suffix&selected&current&EVENTS&QUIET&PREFIX&FINAL&SUFFIX).
        exists(gateway_ambient::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split;[constructor;[right;reflexivity|exact QUIET]|]. split.
        -- econstructor;[apply gateway_interleaved;exact INTERFERENCE|].
           rewrite gateway_memory_replace_twice in PREFIX|-*;exact PREFIX.
        -- split;assumption.
      * destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
