(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Guards and argument loads come from actual source instructions. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight Maps.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayCallPath.
Import ListNotations.

Theorem gateway_source_instruction_occurrence {World Event}(backend:gateway_backend World Event)ge
    function statement continuation environment temporaries before world events returned after final_world :
  ~gateway_at_primitive(State function statement continuation environment temporaries before) ->
  gateway_steps backend ge
    (gateway_live(State function statement continuation environment temporaries before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory instruction_world trace target,
    events=prefix++gateway_source trace::suffix /\
    Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(State function statement continuation environment temporaries before)world)prefix
      (gateway_live(State function statement continuation environment temporaries memory)instruction_world) /\
    step2 ge(State function statement continuation environment temporaries memory)trace target /\
    gateway_steps backend ge(gateway_live target instruction_world)suffix
      (gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  revert before world;induction events as[|event rest IH];intros before world INTERNAL RUN.
  - inversion RUN.
  - inversion RUN as[|first observed middle remaining last HEAD TAIL];subst.
    assert(NOT_PRIMITIVE:~gateway_at_primitive
      (State function statement continuation environment temporaries before)).
    { intro BAD;apply INTERNAL;exact BAD. }
    destruct(gateway_nonprimitive_step backend ge _ _ _ _ NOT_PRIMITIVE HEAD)
      as[[trace[target[EVENT[REAL TARGET]]]]|
        [[changed[next[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + exists[],rest,before,world,trace,target;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + cbn[gateway_replace_memory]in TAIL.
      destruct(IH changed next ltac:(exact INTERNAL)TAIL)
        as[prefix[suffix[memory[instruction_world[trace[target[EVENTS[AMBIENT[PREFIX[REAL REST]]]]]]]]]].
      exists(gateway_ambient::prefix),suffix,memory,instruction_world,trace,target.
      split;[cbn;congruence|]. split;[constructor;[reflexivity|exact AMBIENT]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;assumption.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

Theorem gateway_uniform_instruction_next {World Event}(backend:gateway_backend World Event)ge
    function statement continuation environment temporaries before world events returned after final_world target :
  ~gateway_at_primitive(State function statement continuation environment temporaries before) ->
  (forall memory,store_edge ge(State function statement continuation environment temporaries memory)
    (gateway_replace_memory target memory)) ->
  gateway_steps backend ge
    (gateway_live(State function statement continuation environment temporaries before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory instruction_world,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(State function statement continuation environment temporaries before)world)prefix
      (gateway_live(State function statement continuation environment temporaries memory)instruction_world) /\
    gateway_steps backend ge(gateway_live(gateway_replace_memory target memory)instruction_world)suffix
      (gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  intros INTERNAL EDGES RUN.
  destruct(gateway_source_instruction_occurrence backend ge function statement continuation environment
    temporaries before world events returned after final_world INTERNAL RUN)
    as[prefix[suffix[memory[instruction_world[trace[next[EVENTS[AMBIENT[PREFIX[REAL REST]]]]]]]]]].
  destruct(EDGES memory)as[IN[CANON UNIQUE]].
  destruct(UNIQUE _ _ REAL)as[SAME TARGET];subst trace next.
  exists prefix,suffix,memory,instruction_world;auto.
Qed.

Theorem gateway_set_result_cut {World Event}(backend:gateway_backend World Event)ge
    function identifier expression continuation environment temporaries before world events returned after final_world :
  gateway_steps backend ge
    (gateway_live(State function(Sset identifier expression)continuation environment temporaries before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory instruction_world value,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(State function(Sset identifier expression)continuation environment temporaries before)world)prefix
      (gateway_live(State function(Sset identifier expression)continuation environment temporaries memory)instruction_world) /\
    eval_expr ge environment temporaries memory expression value /\
    gateway_steps backend ge
      (gateway_live(State function Sskip continuation environment(PTree.set identifier value temporaries)memory)instruction_world)
      suffix(gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  intro RUN.
  destruct(gateway_source_instruction_occurrence backend ge function(Sset identifier expression)
    continuation environment temporaries before world events returned after final_world ltac:(cbn;tauto)RUN)
    as[prefix[suffix[memory[instruction_world[trace[next[EVENTS[AMBIENT[PREFIX[REAL REST]]]]]]]]]].
  inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
  match goal with VALUE:eval_expr _ _ _ _ expression ?value|-_=>
    exists prefix,suffix,memory,instruction_world,value end.
  repeat split;assumption.
Qed.
