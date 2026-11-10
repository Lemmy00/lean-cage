(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Retained source prefixes add no hidden receive observations. *)
From Stdlib Require Import List ZArith.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayFrames GatewayCallPath GatewayOperations.
Import ListNotations.

Inductive gateway_guarded_retained_path (ge:Clight.genv)(property:mem->Prop)
    (definition:Ctypes.fundef Clight.function)(arguments:list val)(continuation:cont):Clight.state->Prop:=
|gateway_guarded_reached:forall memory,
  gateway_guarded_retained_path ge property definition arguments continuation
    (Callstate definition arguments continuation memory)
|gateway_guarded_next:forall source next,
  ~gateway_at_primitive source ->
  (forall memory,property memory->store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next memory)) ->
  gateway_guarded_retained_path ge property definition arguments continuation next ->
  gateway_guarded_retained_path ge property definition arguments continuation source.

Lemma gateway_guarded_replace ge property definition arguments continuation source memory :
  gateway_guarded_retained_path ge property definition arguments continuation source ->
  gateway_guarded_retained_path ge property definition arguments continuation(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;induction SCRIPT;cbn;[constructor|].
  eapply gateway_guarded_next with(next:=gateway_replace_memory next memory).
  - intro PRIMITIVE;apply H;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
  - intros another GOOD;rewrite !gateway_memory_replace_twice;apply H0;exact GOOD.
  - exact IHSCRIPT.
Qed.

Theorem gateway_guarded_ready_cut {World Event}(backend:gateway_backend World Event)ge
    property definition arguments continuation(ready:mem->World->Prop)
    (discipline:gateway_runtime_discipline backend ready)
    (sufficient:forall memory world,ready memory world->property memory)
    source world events returned after final_world :
  ready(memory_of source)world ->gateway_guarded_retained_path ge property definition arguments continuation source ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory called_world,
    events=prefix++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    gateway_steps backend ge(gateway_live source world)prefix
      (gateway_live(Callstate definition arguments continuation memory)called_world) /\
    ready memory called_world /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments continuation memory)called_world)suffix
      (gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  revert source world;induction events as[|event rest IH];intros source world READY SCRIPT RUN.
  - inversion RUN;subst;inversion SCRIPT;subst.
    match goal with EDGES:forall memory,property memory->_|-_=>
      destruct(EDGES after(sufficient after final_world READY))as[_[REAL _]]end;cbn in REAL;inversion REAL.
  - inversion SCRIPT;subst.
    + exists[],(event::rest),memory,world;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + inversion RUN;subst.
      match goal with STEP:gateway_step _ _ _ _ _|-_=>
        destruct(gateway_nonprimitive_step _ _ _ _ _ _ H STEP)
          as[[trace[next_source[EVENT[REAL TARGET]]]]|
            [[changed[next_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]]end;subst.
      * destruct(H0(memory_of source)(sufficient _ _ READY))as[IN[CANON UNIQUE]].
        rewrite gateway_memory_replace_identity in IN,CANON,UNIQUE.
        destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst trace next_source.
        assert(NEXT_READY:ready(memory_of(gateway_replace_memory next(memory_of source)))world).
        { rewrite gateway_replace_memory_of;exact READY. }
        destruct(IH(gateway_replace_memory next(memory_of source))world NEXT_READY
          ltac:(apply gateway_guarded_replace;assumption)ltac:(assumption))
          as[prefix[suffix[memory[called_world[EVENTS[PURE[PREFIX[RESULT SUFFIX]]]]]]]].
        exists(gateway_source E0::prefix),suffix,memory,called_world.
        split;[cbn;congruence|]. split;[constructor;[left;reflexivity|exact PURE]|]. split.
        -- econstructor;[apply gateway_internal;[exact IN|exact REAL]|exact PREFIX].
        -- auto.
      * assert(NEXT_READY:ready(memory_of(gateway_replace_memory source changed))next_world).
        { rewrite gateway_replace_memory_of;eapply discipline;[exact READY|exact INTERFERENCE]. }
        destruct(IH(gateway_replace_memory source changed)next_world NEXT_READY
          ltac:(apply gateway_guarded_replace;exact SCRIPT)ltac:(assumption))
          as[prefix[suffix[memory[called_world[EVENTS[PURE[PREFIX[RESULT SUFFIX]]]]]]]].
        exists(gateway_ambient::prefix),suffix,memory,called_world.
        split;[cbn;congruence|]. split;[constructor;[right;reflexivity|exact PURE]|]. split.
        -- econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
        -- auto.
      * match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
          destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.
