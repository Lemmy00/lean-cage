(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Recover the actual local-allocation frontier from one wider run. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts.
Import ListNotations.

Lemma gateway_function_call_step {World Event}(backend:gateway_backend World Event)ge
    function arguments continuation before world observed target :
  gateway_step backend ge
    (gateway_live(Callstate(Internal function)arguments continuation before)world)observed target ->
  (exists environment temporaries after,observed=gateway_source E0 /\
    function_entry2 ge function arguments before environment temporaries after /\
    target=gateway_live(State function(fn_body function)continuation environment temporaries after)world) \/
  (exists after next,observed=gateway_ambient /\
    gateway_interference backend before world after next /\
    target=gateway_live(Callstate(Internal function)arguments continuation after)next) \/
  (observed=gateway_lost /\target=gateway_dead before world).
Proof.
  intro STEP;inversion STEP;subst.
  - match goal with REAL:step2 _ (Callstate(Internal _) _ _ _)_ _|-_=>inversion REAL;subst end.
    match goal with ENTRY:function_entry2 _ _ _ _ ?environment ?temporaries ?after|-_=>
      left;exists environment,temporaries,after;split;[reflexivity|];split;[exact ENTRY|reflexivity]end.
  - right;left;eexists;eexists;repeat split;eauto.
  - cbn in *;contradiction.
  - right;right;auto.
Qed.

Theorem actual_gateway_function_entry_ambient {World Event}(backend:gateway_backend World Event)ge
    function arguments continuation before world events value returned_cont after final_world :
  gateway_steps backend ge
    (gateway_live(Callstate(Internal function)arguments continuation before)world)events
    (gateway_live(Returnstate value returned_cont after)final_world) ->
  exists prefix suffix entry_memory entry_world environment temporaries allocated,
    events=prefix++gateway_source E0::suffix /\
    Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal function)arguments continuation before)world)prefix
      (gateway_live(Callstate(Internal function)arguments continuation entry_memory)entry_world) /\
    function_entry2 ge function arguments entry_memory environment temporaries allocated /\
    gateway_steps backend ge
      (gateway_live(State function(fn_body function)continuation environment temporaries allocated)entry_world)
      suffix(gateway_live(Returnstate value returned_cont after)final_world).
Proof.
  revert before world;induction events as[|observed rest IH];intros before world RUN.
  - inversion RUN.
  - inversion RUN;subst.
    match goal with STEP:gateway_step _ _ _ _ _|-_=>
      destruct(gateway_function_call_step _ _ _ _ _ _ _ _ _ STEP)
        as[[environment[temporaries[allocated[EVENT[ENTRY TARGET]]]]]|
          [[changed[next[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]]end;subst.
    + exists[],rest,before,world,environment,temporaries,allocated;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + match goal with TAIL:gateway_steps _ _
          (gateway_live(Callstate(Internal _) _ _ changed)next)_ _|-_=>
        destruct(IH changed next TAIL)as[prefix[suffix[entry_memory[entry_world
          [environment[temporaries[allocated[EVENTS[AMBIENT[PREFIX[ENTRY SUFFIX]]]]]]]]]]]end.
      exists(gateway_ambient::prefix),suffix,entry_memory,entry_world,environment,temporaries,allocated.
      split;[cbn;congruence|]. split;[constructor;[reflexivity|exact AMBIENT]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;assumption.
    + match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
        destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

Theorem actual_gateway_function_entry {World Event}(backend:gateway_backend World Event)ge
    function arguments continuation before world events value returned_cont after final_world :
  gateway_steps backend ge
    (gateway_live(Callstate(Internal function)arguments continuation before)world)events
    (gateway_live(Returnstate value returned_cont after)final_world) ->
  exists prefix suffix entry_memory entry_world environment temporaries allocated,
    events=prefix++gateway_source E0::suffix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal function)arguments continuation before)world)prefix
      (gateway_live(Callstate(Internal function)arguments continuation entry_memory)entry_world) /\
    function_entry2 ge function arguments entry_memory environment temporaries allocated /\
    gateway_steps backend ge
      (gateway_live(State function(fn_body function)continuation environment temporaries allocated)entry_world)
      suffix(gateway_live(Returnstate value returned_cont after)final_world).
Proof.
  intro RUN;destruct(actual_gateway_function_entry_ambient backend ge function arguments continuation
    before world events value returned_cont after final_world RUN)
    as[prefix[suffix[entry_memory[entry_world[environment[temporaries[allocated
      [EVENTS[AMBIENT[PREFIX[ENTRY SUFFIX]]]]]]]]]]].
  exists prefix,suffix,entry_memory,entry_world,environment,temporaries,allocated;auto.
Qed.
