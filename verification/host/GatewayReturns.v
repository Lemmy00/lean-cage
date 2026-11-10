(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Failures cannot become successful returns after memory interference. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayCallPath.
Import ListNotations.

Theorem gateway_return_value_fixed {World Event}(backend:gateway_backend World Event)ge
    value before world events actual after final_world :
  gateway_steps backend ge(gateway_live(Returnstate value Kstop before)world)events
    (gateway_live(Returnstate actual Kstop after)final_world) ->actual=value.
Proof.
  revert before world;induction events as[|event rest IH];intros before world RUN.
  - inversion RUN;reflexivity.
  - inversion RUN;subst.
    match goal with STEP:gateway_step _ _ _ _ _|-_=>inversion STEP;subst end;cbn in *;try contradiction.
    + match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
    + eapply IH;eassumption.
    + match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
        destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

Theorem gateway_constant_return {World Event}(backend:gateway_backend World Event)ge
    function expression continuation environment temporaries memory world value converted events actual after final_world :
  call_cont continuation=Kstop ->
  (forall memory,expression_value ge environment temporaries memory expression value) ->
  (forall memory,sem_cast value(typeof expression)(fn_return function)memory=Some converted) ->
  gateway_steps backend ge
    (gateway_live(State function(Sreturn(Some expression))continuation environment temporaries memory)world)events
    (gateway_live(Returnstate actual Kstop after)final_world) ->actual=converted.
Proof.
  intros CONTINUATION EXPRESSION CAST;revert memory world;induction events as[|event rest IH];intros memory world RUN.
  - inversion RUN.
  - inversion RUN as[|first observed middle remaining last HEAD TAIL];subst.
    assert(INTERNAL:~gateway_at_primitive
      (State function(Sreturn(Some expression))continuation environment temporaries memory))by(cbn;tauto).
    destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
      as[[trace[next_source[EVENT[REAL TARGET]]]]|
        [[changed[next_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
      match goal with EVALUATION:eval_expr _ _ _ _ expression ?returned|-_=>
        destruct(EXPRESSION memory)as[_ UNIQUE];pose proof(UNIQUE _ EVALUATION)as SAME;subst returned end.
      match goal with CONVERSION:sem_cast value _ _ _=Some ?returned|-_=>
        rewrite(CAST memory)in CONVERSION;inversion CONVERSION;subst returned end.
      rewrite CONTINUATION in *;eapply gateway_return_value_fixed;eassumption.
    + eapply IH;eassumption.
    + match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
        destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

Inductive gateway_constant_path (ge:Clight.genv)(result:val) : Clight.state->Prop :=
| gateway_constant_at_return : forall function expression continuation environment temporaries memory value,
    call_cont continuation=Kstop ->
    (forall memory,expression_value ge environment temporaries memory expression value) ->
    (forall memory,sem_cast value(typeof expression)(fn_return function)memory=Some result) ->
    gateway_constant_path ge result
      (State function(Sreturn(Some expression))continuation environment temporaries memory)
| gateway_constant_next : forall source next,
    ~gateway_at_primitive source ->
    (forall memory,store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next memory)) ->
    gateway_constant_path ge result next ->gateway_constant_path ge result source.

Lemma gateway_constant_path_replace ge result source memory :
  gateway_constant_path ge result source ->
  gateway_constant_path ge result(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;induction SCRIPT;cbn.
  - econstructor;eassumption.
  - eapply gateway_constant_next with(next:=gateway_replace_memory next memory).
    + intro PRIMITIVE;apply H;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
    + intro another;rewrite !gateway_memory_replace_twice;apply H0.
    + exact IHSCRIPT.
Qed.

Theorem gateway_constant_path_actual {World Event}(backend:gateway_backend World Event)ge
    source result world events actual after final_world :
  gateway_constant_path ge result source ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate actual Kstop after)final_world) ->actual=result.
Proof.
  revert source world;induction events as[|event rest IH];intros source world SCRIPT RUN.
  - inversion RUN;subst;inversion SCRIPT;subst.
    match goal with EDGES:forall memory,store_edge _ _ _|-_=>
      destruct(EDGES after)as[_[REAL _]]end;cbn in REAL;inversion REAL.
  - inversion SCRIPT;subst.
    + eapply gateway_constant_return;eassumption.
    + inversion RUN;subst.
      match goal with STEP:gateway_step _ _ _ _ _|-_=>
        destruct(gateway_nonprimitive_step _ _ _ _ _ _ H STEP)
          as[[trace[next_source[EVENT[REAL TARGET]]]]|
            [[changed[next_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]]end;subst.
      * match goal with EDGES:forall memory,store_edge _ _ _|-_=>
          destruct(EDGES(memory_of source))as[_[_ UNIQUE]]end.
        rewrite gateway_memory_replace_identity in UNIQUE.
        destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst.
        eapply IH;[apply gateway_constant_path_replace;eassumption|eassumption].
      * eapply IH;[apply gateway_constant_path_replace;exact SCRIPT|eassumption].
      * match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
          destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

Inductive gateway_blocked_path(ge:Clight.genv):Clight.state->Prop:=
| gateway_blocked_at:forall source,
    ~gateway_at_primitive source ->
    (forall value continuation memory,source<>Returnstate value continuation memory) ->
    (forall memory trace target,~step2 ge(gateway_replace_memory source memory)trace target) ->
    gateway_blocked_path ge source
| gateway_blocked_next:forall source next,
    ~gateway_at_primitive source ->
    (forall memory,store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next memory)) ->
    gateway_blocked_path ge next ->gateway_blocked_path ge source.

Lemma gateway_blocked_replace ge source memory :
  gateway_blocked_path ge source ->gateway_blocked_path ge(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;induction SCRIPT.
  - constructor.
    + intro PRIMITIVE;apply H;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
    + destruct source;cbn in *;try(intros;discriminate).
      exfalso;eapply H0;reflexivity.
    + intros another trace target;rewrite gateway_memory_replace_twice;apply H1.
  - eapply gateway_blocked_next with(next:=gateway_replace_memory next memory).
    + intro PRIMITIVE;apply H;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
    + intro another;rewrite !gateway_memory_replace_twice;apply H0.
    + exact IHSCRIPT.
Qed.

Theorem gateway_blocked_cannot_return {World Event}(backend:gateway_backend World Event)ge
    source world events value after next :
  gateway_blocked_path ge source ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate value Kstop after)next) ->Logic.False.
Proof.
  revert source world;induction events as[|observed rest IH];intros source world SCRIPT RUN.
  - inversion RUN;subst;inversion SCRIPT;subst.
    + eapply H0;reflexivity.
    + destruct(H0 after)as[_[REAL _]];cbn in REAL;inversion REAL.
  - inversion RUN as[|first event middle remaining target HEAD TAIL];subst.
    assert(INTERNAL:~gateway_at_primitive source)by(inversion SCRIPT;assumption).
    destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
      as[[trace[following[EVENT[REAL TARGET]]]]|
        [[changed[following_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion SCRIPT;subst.
      * apply(H1(memory_of source)trace following);rewrite gateway_memory_replace_identity;exact REAL.
      * destruct(H0(memory_of source))as[_[_ UNIQUE]].
        rewrite gateway_memory_replace_identity in UNIQUE.
        destruct(UNIQUE _ _ REAL)as[ZERO SAME];subst.
        eapply IH;[apply gateway_blocked_replace;eassumption|exact TAIL].
    + eapply IH;[apply gateway_blocked_replace;exact SCRIPT|exact TAIL].
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
