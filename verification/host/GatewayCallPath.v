(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: The first callback is extracted from the same wider source run. *)
From Stdlib Require Import List ZArith.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayFrames.
Import ListNotations.

Inductive gateway_call_path (ge:Clight.genv)(protected:block->Z->Prop)
    (definition:Ctypes.fundef Clight.function)(arguments:list val)(continuation:cont)
    (result:mem->Prop) : (mem->Prop)->Clight.state->Prop :=
| gateway_call_reached : forall property memory,
    gateway_region_closed protected property ->
    (forall memory,property memory->result memory) ->
    gateway_call_path ge protected definition arguments continuation result property
      (Callstate definition arguments continuation memory)
| gateway_call_next : forall property source next middle,
    gateway_region_closed protected property -> ~gateway_at_primitive source ->
    (forall memory,property memory -> exists after,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next after) /\ middle after) ->
    gateway_call_path ge protected definition arguments continuation result middle next ->
    gateway_call_path ge protected definition arguments continuation result property source.

Lemma gateway_call_path_replace ge protected definition arguments continuation result property source memory :
  gateway_call_path ge protected definition arguments continuation result property source ->
  gateway_call_path ge protected definition arguments continuation result property
    (gateway_replace_memory source memory).
Proof.
  intro SCRIPT;induction SCRIPT;cbn.
  - constructor;assumption.
  - eapply gateway_call_next with(next:=gateway_replace_memory next memory)(middle:=middle).
    + exact H.
    + intro PRIMITIVE;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
    + intros another GOOD;rewrite gateway_memory_replace_twice.
      destruct(H1 another GOOD)as[after[EDGE POST]].
      exists after;rewrite gateway_memory_replace_twice;auto.
    + exact IHSCRIPT.
Qed.

Lemma gateway_call_same ge protected definition arguments continuation result property source next :
  gateway_region_closed protected property ->~gateway_at_primitive source ->
  (forall memory,property memory ->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory next memory)) ->
  gateway_call_path ge protected definition arguments continuation result property next ->
  gateway_call_path ge protected definition arguments continuation result property source.
Proof.
  intros CLOSED INTERNAL EDGE REST.
  eapply gateway_call_next with(next:=next)(middle:=property);[exact CLOSED|exact INTERNAL| |exact REST].
  intros memory GOOD;exists memory;auto.
Qed.

Lemma gateway_nonprimitive_step {World Event}(backend:gateway_backend World Event)ge
    source world observed target :
  ~gateway_at_primitive source ->gateway_step backend ge(gateway_live source world)observed target ->
  (exists trace next,observed=gateway_source trace /\step2 ge source trace next /\
    target=gateway_live next world) \/
  (exists after next,observed=gateway_ambient /\
    gateway_interference backend(memory_of source)world after next /\
    target=gateway_live(gateway_replace_memory source after)next) \/
  (observed=gateway_lost /\target=gateway_dead(memory_of source)world).
Proof.
  intros INTERNAL STEP;inversion STEP;subst.
  - left;eexists;eexists;repeat split;eauto.
  - exfalso;apply INTERNAL;exact I.
  - exfalso;apply INTERNAL;exact I.
  - right;left;eexists;eexists;repeat split;eauto.
  - contradiction.
  - right;right;auto.
  - exfalso;apply INTERNAL;exact I.
  - exfalso;apply INTERNAL;exact I.
Qed.

Theorem gateway_call_path_cut {World Event}(backend:gateway_backend World Event)ge protected active
    (law:gateway_private_contract backend protected active)definition arguments continuation result
    property source world events returned after final_world :
  active world ->property(memory_of source) ->
  gateway_call_path ge protected definition arguments continuation result property source ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory called_world,
    events=prefix++suffix /\
    gateway_steps backend ge(gateway_live source world)prefix
      (gateway_live(Callstate definition arguments continuation memory)called_world) /\
    result memory /\active called_world /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments continuation memory)called_world)
      suffix(gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  revert property source world;induction events as[|event rest IH];
    intros property source world ACTIVE PROPERTY SCRIPT RUN.
  - inversion RUN;subst;inversion SCRIPT;subst.
    match goal with EDGES:forall memory,property memory->_|-_=>
      destruct(EDGES after PROPERTY)as[changed[[_[REAL _]]POST]]end.
    cbn in REAL;inversion REAL.
  - inversion SCRIPT;subst.
    + exists[],(event::rest),memory,world;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[auto|]. split;assumption.
    + inversion RUN;subst.
      match goal with STEP:gateway_step _ _ _ _ _|-_=>
        destruct(gateway_nonprimitive_step _ _ _ _ _ _ H0 STEP)
          as[[trace[next_source[EVENT[REAL TARGET]]]]|
            [[changed[next_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]]end;subst.
      * match goal with EDGES:forall memory,property memory->_|-_=>
          destruct(EDGES(memory_of source)PROPERTY)as[changed[[IN[CANON UNIQUE]]POST]]end.
        rewrite gateway_memory_replace_identity in IN,CANON,UNIQUE.
        destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst trace next_source.
        destruct(IH middle(gateway_replace_memory next changed)world ACTIVE
          ltac:(rewrite gateway_replace_memory_of;exact POST)
          ltac:(apply gateway_call_path_replace;assumption)ltac:(assumption))
          as[prefix[suffix[memory[called_world[EVENTS[PREFIX[RESULT[ALIVE SUFFIX]]]]]]]].
        exists(gateway_source Events.E0::prefix),suffix,memory,called_world.
        split;[cbn;congruence|]. split.
        -- econstructor;[apply gateway_internal;[exact IN|exact REAL]|exact PREFIX].
        -- auto.
      * destruct(gateway_private_ambient _ _ _ law _ _ _ _ ACTIVE INTERFERENCE)as[NEXT FRAME].
        destruct(IH property(gateway_replace_memory source changed)next_world NEXT
          ltac:(rewrite gateway_replace_memory_of;eapply H;eassumption)
          ltac:(apply gateway_call_path_replace;exact SCRIPT)ltac:(assumption))
          as[prefix[suffix[memory[called_world[EVENTS[PREFIX[RESULT[ALIVE SUFFIX]]]]]]]].
        exists(gateway_ambient::prefix),suffix,memory,called_world.
        split;[cbn;congruence|]. split.
        -- econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
        -- auto.
      * match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
          destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

(* This variant needs no memory frame: every next instruction is certified for
   every memory, so arbitrary ambient memory/world changes remain possible. *)
Inductive gateway_control_call_path (ge:Clight.genv)(definition:Ctypes.fundef Clight.function)
    (arguments:list val)(continuation:cont) : Clight.state->Prop :=
| gateway_control_call_reached : forall memory,
    gateway_control_call_path ge definition arguments continuation
      (Callstate definition arguments continuation memory)
| gateway_control_call_next : forall source next,
    ~gateway_at_primitive source ->
    (forall memory,exists after,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next after)) ->
    gateway_control_call_path ge definition arguments continuation next ->
    gateway_control_call_path ge definition arguments continuation source.

Lemma gateway_control_call_replace ge definition arguments continuation source memory :
  gateway_control_call_path ge definition arguments continuation source ->
  gateway_control_call_path ge definition arguments continuation(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;induction SCRIPT;cbn;[constructor|].
  eapply gateway_control_call_next with(next:=gateway_replace_memory next memory).
  - intro PRIMITIVE;apply H;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
  - intro another;rewrite gateway_memory_replace_twice;destruct(H0 another)as[changed EDGE].
    exists changed;rewrite gateway_memory_replace_twice;exact EDGE.
  - exact IHSCRIPT.
Qed.

Theorem gateway_control_call_cut {World Event}(backend:gateway_backend World Event)ge
    definition arguments continuation source world events returned after final_world :
  gateway_control_call_path ge definition arguments continuation source ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory called_world,events=prefix++suffix /\
    gateway_steps backend ge(gateway_live source world)prefix
      (gateway_live(Callstate definition arguments continuation memory)called_world) /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments continuation memory)called_world)
      suffix(gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  revert source world;induction events as[|event rest IH];intros source world SCRIPT RUN.
  - inversion RUN;subst;inversion SCRIPT;subst.
    match goal with EDGES:forall memory,exists after,store_edge _ _ _|-_=>
      destruct(EDGES after)as[changed[_[REAL _]]]end;cbn in REAL;inversion REAL.
  - inversion SCRIPT;subst.
    + exists[],(event::rest),memory,world;cbn;split;[reflexivity|]. split;[constructor|exact RUN].
    + inversion RUN;subst.
      match goal with STEP:gateway_step _ _ _ _ _|-_=>
        destruct(gateway_nonprimitive_step _ _ _ _ _ _ H STEP)
          as[[trace[next_source[EVENT[REAL TARGET]]]]|
            [[changed[next_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]]end;subst.
      * match goal with EDGES:forall memory,exists after,store_edge _ _ _|-_=>
          destruct(EDGES(memory_of source))as[changed[IN[CANON UNIQUE]]]end.
        rewrite gateway_memory_replace_identity in IN,CANON,UNIQUE.
        destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst trace next_source.
        destruct(IH(gateway_replace_memory next changed)world
          ltac:(apply gateway_control_call_replace;assumption)ltac:(assumption))
          as[prefix[suffix[memory[called_world[EVENTS[PREFIX SUFFIX]]]]]].
        exists(gateway_source E0::prefix),suffix,memory,called_world.
        split;[cbn;congruence|]. split.
        -- econstructor;[apply gateway_internal;[exact IN|exact REAL]|exact PREFIX].
        -- exact SUFFIX.
      * destruct(IH(gateway_replace_memory source changed)next_world
          ltac:(apply gateway_control_call_replace;exact SCRIPT)ltac:(assumption))
          as[prefix[suffix[memory[called_world[EVENTS[PREFIX SUFFIX]]]]]].
        exists(gateway_ambient::prefix),suffix,memory,called_world.
        split;[cbn;congruence|]. split.
        -- econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
        -- exact SUFFIX.
      * match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
          destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

Inductive gateway_retained_call_path (ge:Clight.genv)(definition:Ctypes.fundef Clight.function)
    (arguments:list val)(continuation:cont) :Clight.state->Prop:=
| gateway_retained_call:forall memory,gateway_retained_call_path ge definition arguments continuation
    (Callstate definition arguments continuation memory)
| gateway_retained_next:forall source next,
    ~gateway_at_primitive source ->
    (forall memory,store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next memory)) ->
    gateway_retained_call_path ge definition arguments continuation next ->
    gateway_retained_call_path ge definition arguments continuation source.

Lemma gateway_retained_control ge definition arguments continuation source :
  gateway_retained_call_path ge definition arguments continuation source ->
  gateway_control_call_path ge definition arguments continuation source.
Proof.
  intro SCRIPT;induction SCRIPT;[constructor|].
  eapply gateway_control_call_next;[exact H| |exact IHSCRIPT].
  intro memory;exists memory;apply H0.
Qed.

Lemma gateway_retained_framed ge definition arguments continuation source protected property :
  gateway_retained_call_path ge definition arguments continuation source ->
  gateway_region_closed protected property ->
  gateway_call_path ge protected definition arguments continuation property property source.
Proof.
  intros SCRIPT CLOSED;induction SCRIPT.
  - constructor;[exact CLOSED|auto].
  - eapply gateway_call_same;[exact CLOSED|exact H| |exact IHSCRIPT].
    intros memory GOOD;apply H0.
Qed.
