(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A pending later call retains the real callee's local allocation. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayFunctionEntry GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_entry_before_frontier {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)
    function arguments continuation before world events target next:
  (forall memory,Callstate(Internal function)arguments continuation memory<>target)->
  property before world->
  gateway_steps backend ge(gateway_live(Callstate(Internal function)arguments continuation before)world)events
    (gateway_live target next)->
  exists pending rest memory current environment temporaries allocated,
    events=pending++gateway_source E0::rest /\Forall(fun event=>event=gateway_ambient)pending /\
    gateway_steps backend ge(gateway_live(Callstate(Internal function)arguments continuation before)world)pending
      (gateway_live(Callstate(Internal function)arguments continuation memory)current) /\property memory current /\
    function_entry2 ge function arguments memory environment temporaries allocated /\
    gateway_steps backend ge(gateway_live(State function(fn_body function)continuation environment temporaries allocated)current)
      rest(gateway_live target next).
Proof.
  intros DIFFERENT;revert before world.
  induction events as[|event rest IH];intros before world READY RUN.
  - inversion RUN;subst;exfalso;apply(DIFFERENT before);reflexivity.
  - inversion RUN as[|first observed middle remaining last HEAD TAIL];subst.
    destruct(gateway_function_call_step backend ge function arguments continuation before world event middle HEAD)
      as[[environment[temporaries[allocated[EVENT[ENTRY TARGET]]]]]|
        [[memory[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + exists[],rest,before,world,environment,temporaries,allocated;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;[exact READY|]. split;assumption.
    + destruct(IH memory current(CLOSED _ _ _ _ READY INTERFERENCE)TAIL)
        as(prefix&suffix&called&owner&environment&temporaries&allocated&EVENTS&AMBIENT&PREFIX&CALLED&ENTRY&SUFFIX).
      exists(gateway_ambient::prefix),suffix,called,owner,environment,temporaries,allocated.
      split;[cbn;congruence|]. split;[constructor;[reflexivity|exact AMBIENT]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;[exact CALLED|]. split;assumption.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
