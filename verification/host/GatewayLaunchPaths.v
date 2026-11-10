(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Setup callbacks and error branches share one actual spawn prefix. *)
From Stdlib Require Import List Lia Wf_nat.
From compcert Require Import Maps AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPure GatewayFrames
  GatewayOperations GatewayCallPath GatewayReturnBarrier GatewayLaunchHelpers GatewaySpawnABI GatewayFramedRuntime GatewaySymbolicBarrier.
Import ListNotations.

Definition gateway_launch_not_spawn(source:Clight.state):Prop:=
  match source with
  |Callstate definition _ _ _=>definition<>gateway_spawn_signature gateway_posix_spawn_api
  |_=>True end.

Inductive gateway_launch_path {World Event}(backend:gateway_backend World Event)
    (target:Clight.state->World->Prop):(mem->World->Prop)->Clight.state->Prop:=
|gateway_launch_reached:forall property source,
    (forall memory world,property memory world->target(gateway_replace_memory source memory)world)->
    gateway_launch_path backend target property source
|gateway_launch_failure:forall property owner environment allowed body continuation temporaries memory,
    gateway_barrier_bindings(Clight.globalenv prog)environment allowed(gateway_spawn_signature gateway_posix_spawn_api)->
    gateway_barrier_returns allowed body->call_cont continuation=Kstop->
    gateway_launch_path backend target property(State owner body continuation environment temporaries memory)
|gateway_launch_symbolic_failure:forall property owner environment allowed protected word body continuation temporaries memory,
    gateway_barrier_bindings(Clight.globalenv prog)environment allowed(gateway_spawn_signature gateway_posix_spawn_api)->
    Integers.Int.eq word Integers.Int.zero=false->temporaries!protected=Some(Vint word)->
    gateway_symbolic_returns allowed protected body->call_cont continuation=Kstop->
    gateway_launch_path backend target property(State owner body continuation environment temporaries memory)
|gateway_launch_stuck:forall property source,
    gateway_ambient_closed backend property->~gateway_at_primitive source->gateway_launch_not_spawn source->
    (forall memory world trace after,property memory world->
      ~step2(Clight.globalenv prog)(gateway_replace_memory source memory)trace after)->
    gateway_launch_path backend target property source
|gateway_launch_next:forall property source following middle,
    gateway_ambient_closed backend property->~gateway_at_primitive source->gateway_launch_not_spawn source->
    (forall memory world,property memory world->exists after,
      store_edge(Clight.globalenv prog)(gateway_replace_memory source memory)(gateway_replace_memory following after) /\
      middle after world)->
    gateway_launch_path backend target middle following->
    gateway_launch_path backend target property source
|gateway_launch_external:forall property external types result convention arguments continuation memory,
    External external types result convention<>gateway_spawn_signature gateway_posix_spawn_api->
    gateway_ambient_closed backend property->
    (forall before world returned after next observed,
      property before world->gateway_external backend external types result convention arguments
        before world returned after next observed->
      exists middle,middle after next /\gateway_launch_path backend target middle(Returnstate returned continuation after))->
    gateway_launch_path backend target property
      (Callstate(External external types result convention)arguments continuation memory)
|gateway_launch_helper_call:forall property helper arguments continuation memory,
    is_call_cont continuation->
    (forall before world events returned after next,
      property before world->
      gateway_steps backend(Clight.globalenv prog)
        (gateway_live(Callstate(Internal(gateway_launch_function helper))arguments Kstop before)world)events
        (gateway_live(Returnstate returned Kstop after)next)->
      exists middle,middle after next /\gateway_launch_path backend target middle(Returnstate returned continuation after))->
    gateway_launch_path backend target property
      (Callstate(Internal(gateway_launch_function helper))arguments continuation memory).

Lemma gateway_launch_not_spawn_replace source memory:
  gateway_launch_not_spawn source->gateway_launch_not_spawn(gateway_replace_memory source memory).
Proof. destruct source;cbn;tauto. Qed.

Lemma gateway_launch_path_replace {World Event}(backend:gateway_backend World Event)target property source memory:
  gateway_launch_path backend target property source->
  gateway_launch_path backend target property(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;inversion SCRIPT;subst;cbn.
  - eapply gateway_launch_reached;intros before world READY.
    rewrite gateway_memory_replace_twice;apply H;exact READY.
  - eapply gateway_launch_failure;eassumption.
  - eapply gateway_launch_symbolic_failure;eassumption.
  - eapply gateway_launch_stuck.
    + exact H.
    + intro BAD;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))BAD).
    + apply gateway_launch_not_spawn_replace;exact H1.
    + intros before world trace after READY;rewrite gateway_memory_replace_twice;apply H2 with(world:=world);exact READY.
  - eapply gateway_launch_next with(following:=following)(middle:=middle).
    + exact H.
    + intro PRIMITIVE;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
    + apply gateway_launch_not_spawn_replace;exact H1.
    + intros before world READY;rewrite gateway_memory_replace_twice;apply H2;exact READY.
    + exact H3.
  - eapply gateway_launch_external;eassumption.
  - eapply gateway_launch_helper_call;eassumption.
Qed.

Lemma gateway_launch_same {World Event}(backend:gateway_backend World Event)target property source following:
  gateway_ambient_closed backend property->~gateway_at_primitive source->gateway_launch_not_spawn source->
  (forall memory world,property memory world->
    store_edge(Clight.globalenv prog)(gateway_replace_memory source memory)(gateway_replace_memory following memory))->
  gateway_launch_path backend target property following->gateway_launch_path backend target property source.
Proof.
  intros CLOSED INTERNAL NOT_SPAWN EDGE REST.
  eapply gateway_launch_next with(following:=following)(middle:=property);
    [exact CLOSED|exact INTERNAL|exact NOT_SPAWN| |exact REST].
  intros memory world READY;exists memory;split;[apply EDGE with(world:=world);exact READY|exact READY].
Qed.

Lemma gateway_launch_external_step {World Event}(backend:gateway_backend World Event)ge
    external types result convention arguments continuation before world event target:
  gateway_step backend ge(gateway_live(Callstate(External external types result convention)arguments continuation before)world)
    event target->
  (exists returned after next observed,event=gateway_primitive observed /\
    gateway_external backend external types result convention arguments before world returned after next observed /\
    target=gateway_live(Returnstate returned continuation after)next) \/
  (exists after next,event=gateway_ambient /\gateway_interference backend before world after next /\
    target=gateway_live(Callstate(External external types result convention)arguments continuation after)next) \/
  (event=gateway_blocked /\target=gateway_live(Callstate(External external types result convention)arguments continuation before)world) \/
  (exists memory next,target=gateway_dead memory next).
Proof.
  intro STEP;inversion STEP;subst;try contradiction.
  - left;repeat eexists;repeat split;eauto.
  - right;left;repeat eexists;repeat split;eauto.
  - right;right;left;split;reflexivity.
  - right;right;right;repeat eexists.
  - right;right;right;repeat eexists.
Qed.

Theorem gateway_launch_prefix_cut {World Event}(backend:gateway_backend World Event)target
    property source before world events arguments continuation after next:
  gateway_launch_path backend target property source->property before world->
  gateway_steps backend(Clight.globalenv prog)(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists prefix suffix selected current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)(gateway_live(gateway_replace_memory source before)world)prefix
      (gateway_live selected current) /\target selected current /\
    gateway_steps backend(Clight.globalenv prog)(gateway_live selected current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  remember(length events)as size eqn:SIZE.
  revert events SIZE property source before world.
  induction size using lt_wf_ind;intros events SIZE property source before world SCRIPT READY RUN.
  inversion SCRIPT as[reached_property reached_source MATCH|
    failed_property owner environment allowed body failed_cont temporaries template BINDINGS RETURNS STOP|
    symbolic_property owner environment allowed protected word body failed_cont temporaries template BINDINGS NONZERO TEMP RETURNS STOP|
    stuck_property code CLOSED INTERNAL NOT_SPAWN STUCK|
    step_property code following middle CLOSED INTERNAL NOT_SPAWN EDGES REST|
    api_property external types result convention api_arguments api_cont template DIFFERENT CLOSED EFFECT|
    helper_property helper helper_arguments helper_cont template CALL EFFECT];subst.
  - exists[],events,(gateway_replace_memory source before),world;cbn;split;[reflexivity|].
    split;[constructor|]. split;[apply MATCH;exact READY|exact RUN].
  - exfalso;eapply gateway_return_barrier_excludes_call;[exact BINDINGS|exact RETURNS|exact STOP|exact RUN].
  - exfalso;eapply gateway_symbolic_barrier_excludes_call;
      [exact BINDINGS|exact NONZERO|exact TEMP|exact RETURNS|exact STOP|exact RUN].
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
          changed later(gateway_launch_path_replace _ _ _ _ _ SCRIPT)PROPERTY
          ltac:(rewrite gateway_memory_replace_twice;exact TAIL))
          as(prefix&suffix&selected&current&EVENTS&PREFIX&FINAL&SUFFIX).
        exists(gateway_ambient::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split.
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
          as(prefix&suffix&selected&current&EVENTS&PREFIX&FINAL&SUFFIX).
        exists(gateway_source E0::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split.
        -- econstructor;[apply gateway_internal;[exact INTERNAL_SOURCE|exact CANON]|exact PREFIX].
        -- split;assumption.
      * assert(PROPERTY:property changed later).
        { eapply CLOSED;[exact READY|]. rewrite gateway_replace_memory_of in INTERFERENCE;exact INTERFERENCE. }
        rewrite gateway_memory_replace_twice in TAIL.
        destruct(H(length rest)ltac:(cbn;lia)rest eq_refl property(gateway_replace_memory source changed)
          changed later(gateway_launch_path_replace _ _ _ _ _ SCRIPT)PROPERTY
          ltac:(rewrite gateway_memory_replace_twice;exact TAIL))
          as(prefix&suffix&selected&current&EVENTS&PREFIX&FINAL&SUFFIX).
        exists(gateway_ambient::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split.
        -- econstructor;[apply gateway_interleaved;exact INTERFERENCE|].
           rewrite gateway_memory_replace_twice in PREFIX|-*;exact PREFIX.
        -- split;assumption.
      * destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
  - destruct events as[|event rest].
    + inversion RUN;subst;exfalso;apply DIFFERENT;reflexivity.
    + cbn[gateway_replace_memory]in RUN|-*.
      inversion RUN as[|first observed actual_middle remaining last STEP TAIL];subst.
      destruct(gateway_launch_external_step backend(Clight.globalenv prog)external types result convention
        api_arguments api_cont before world event actual_middle STEP)
        as[[returned[changed[later[observed[EVENT[OPERATION TARGET]]]]]]|
          [[changed[later[EVENT[INTERFERENCE TARGET]]]]|[[EVENT TARGET]|[memory[later TARGET]]]]];subst.
      * destruct(EFFECT before world returned changed later observed READY OPERATION)as[middle[POST PATH]].
        destruct(H(length rest)ltac:(cbn;lia)rest eq_refl middle
          (Returnstate returned api_cont changed)changed later PATH POST TAIL)
          as(prefix&suffix&selected&current&EVENTS&PREFIX&FINAL&SUFFIX).
        exists(gateway_primitive observed::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split;[econstructor;[eapply gateway_external_returned;eassumption|exact PREFIX]|].
        split;assumption.
      * assert(PROPERTY:property changed later)by(eapply CLOSED;eassumption).
        destruct(H(length rest)ltac:(cbn;lia)rest eq_refl property
          (Callstate(External external types result convention)api_arguments api_cont changed)changed later
          ltac:(eapply gateway_launch_external;eassumption)PROPERTY TAIL)
          as(prefix&suffix&selected&current&EVENTS&PREFIX&FINAL&SUFFIX).
        exists(gateway_ambient::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split;[econstructor;[apply gateway_interleaved;eassumption|exact PREFIX]|].
        split;assumption.
      * destruct(H(length rest)ltac:(cbn;lia)rest eq_refl property
          (Callstate(External external types result convention)api_arguments api_cont before)before world
          ltac:(eapply gateway_launch_external;eassumption)READY TAIL)
          as(prefix&suffix&selected&current&EVENTS&PREFIX&FINAL&SUFFIX).
        exists(gateway_blocked::prefix),suffix,selected,current.
        split;[cbn;congruence|]. split;[econstructor;[apply gateway_waiting;exact I|exact PREFIX]|].
        split;assumption.
      * destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
  - cbn[gateway_replace_memory]in RUN|-*.
    destruct(actual_launch_helper_return_cut backend helper helper_arguments helper_cont before world events
      arguments continuation after next CALL RUN)
      as(callee_events&caller_events&returned&changed&later&EVENTS&CALLEE&CALLER).
    destruct(EFFECT before world callee_events returned changed later READY CALLEE)as[middle[POST PATH]].
    assert(SHORT:length caller_events<length events).
    { rewrite EVENTS,app_length;destruct callee_events;[inversion CALLEE|cbn;lia]. }
    destruct(H(length caller_events)ltac:(lia)caller_events eq_refl middle
      (Returnstate returned helper_cont changed)changed later PATH POST CALLER)
      as(prefix&suffix&selected&current&TAIL_EVENTS&PREFIX&FINAL&SUFFIX).
    exists(callee_events++prefix),suffix,selected,current.
    split;[rewrite EVENTS,TAIL_EVENTS;apply app_assoc|]. split.
    + eapply gateway_steps_append;[|exact PREFIX].
      exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _ helper_cont CALL CALLEE).
    + split;assumption.
Qed.
