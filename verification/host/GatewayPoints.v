(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual guarded source prefixes reach the selected program point. *)
From Stdlib Require Import List ZArith.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayFrames GatewayCallPath.
Import ListNotations.

Inductive gateway_point_path (ge:Clight.genv)(protected:block->Z->Prop)(point:Clight.state)
    (result:mem->Prop):(mem->Prop)->Clight.state->Prop:=
|gateway_point_reached:forall property memory,
  gateway_region_closed protected property ->(forall memory,property memory->result memory) ->
  gateway_point_path ge protected point result property(gateway_replace_memory point memory)
|gateway_point_next:forall property source next middle,
  gateway_region_closed protected property ->~gateway_at_primitive source ->
  (forall memory,property memory->exists after,
    store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next after) /\middle after) ->
  gateway_point_path ge protected point result middle next ->
  gateway_point_path ge protected point result property source.

Lemma gateway_point_replace ge protected point result property source memory :
  gateway_point_path ge protected point result property source ->
  gateway_point_path ge protected point result property(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;induction SCRIPT.
  - rewrite gateway_memory_replace_twice;constructor;assumption.
  - eapply gateway_point_next with(next:=gateway_replace_memory next memory)(middle:=middle).
    + exact H.
    + intro PRIMITIVE;apply H0;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
    + intros another GOOD;rewrite gateway_memory_replace_twice.
      destruct(H1 another GOOD)as[changed[EDGE POST]].
      exists changed;rewrite gateway_memory_replace_twice;auto.
    + exact IHSCRIPT.
Qed.

Lemma gateway_point_same ge protected point result property source next :
  gateway_region_closed protected property ->~gateway_at_primitive source ->
  (forall memory,property memory->store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory next memory)) ->
  gateway_point_path ge protected point result property next ->
  gateway_point_path ge protected point result property source.
Proof.
  intros CLOSED INTERNAL EDGES REST.
  eapply gateway_point_next with(next:=next)(middle:=property);[exact CLOSED|exact INTERNAL| |exact REST].
  intros memory GOOD;exists memory;auto.
Qed.

Theorem gateway_point_path_cut {World Event}(backend:gateway_backend World Event)ge protected active
    (law:gateway_private_contract backend protected active)point result property source world events
    returned after final_world :
  active world ->property(memory_of source) ->
  gateway_point_path ge protected point result property source ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory point_world,
    events=prefix++suffix /\gateway_steps backend ge(gateway_live source world)prefix
      (gateway_live(gateway_replace_memory point memory)point_world) /\result memory /\active point_world /\
    gateway_steps backend ge(gateway_live(gateway_replace_memory point memory)point_world)suffix
      (gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  revert property source world;induction events as[|event rest IH];
    intros property source world ACTIVE PROPERTY SCRIPT RUN;inversion SCRIPT;subst.
  - exists[],[],(memory_of(gateway_replace_memory point memory)),world.
    rewrite gateway_replace_memory_of in *.
    repeat split;auto using gateway_steps_nil.
  - inversion RUN;subst.
    match goal with EDGES:forall memory,property memory->_|-_=>
      destruct(EDGES after PROPERTY)as[changed[[_[REAL _]]POST]]end.
    cbn in REAL;inversion REAL.
  - exists[],(event::rest),(memory_of(gateway_replace_memory point memory)),world.
    rewrite gateway_replace_memory_of in *.
    repeat split;auto using gateway_steps_nil.
  - inversion RUN;subst.
    match goal with STEP:gateway_step _ _ _ _ _|-_=>
      destruct(gateway_nonprimitive_step _ _ _ _ _ _ H0 STEP)
        as[[trace[next_source[EVENT[REAL TARGET]]]]|
          [[changed[next_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]]end;subst.
    + match goal with EDGES:forall memory,property memory->_|-_=>
        destruct(EDGES(memory_of source)PROPERTY)as[changed[[IN[CANON UNIQUE]]POST]]end.
      rewrite gateway_memory_replace_identity in IN,CANON,UNIQUE.
      destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst trace next_source.
      destruct(IH middle(gateway_replace_memory next changed)world ACTIVE
        ltac:(rewrite gateway_replace_memory_of;exact POST)
        ltac:(apply gateway_point_replace;assumption)ltac:(assumption))
        as[prefix[suffix[memory[point_world[EVENTS[PREFIX[RESULT[ALIVE SUFFIX]]]]]]]].
      exists(gateway_source E0::prefix),suffix,memory,point_world.
      split;[cbn;congruence|]. split.
      * econstructor;[apply gateway_internal;[exact IN|exact REAL]|exact PREFIX].
      * auto.
    + destruct(gateway_private_ambient _ _ _ law _ _ _ _ ACTIVE INTERFERENCE)as[NEXT FRAME].
      destruct(IH property(gateway_replace_memory source changed)next_world NEXT
        ltac:(rewrite gateway_replace_memory_of;eapply H;eassumption)
        ltac:(apply gateway_point_replace;exact SCRIPT)ltac:(assumption))
        as[prefix[suffix[memory[point_world[EVENTS[PREFIX[RESULT[ALIVE SUFFIX]]]]]]]].
      exists(gateway_ambient::prefix),suffix,memory,point_world.
      split;[cbn;congruence|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * auto.
    + match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
        destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.
