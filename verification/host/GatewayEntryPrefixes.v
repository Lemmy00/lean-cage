(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: A selected external call has a real prior native allocation. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayFunctionEntry.
Import ListNotations.

Theorem actual_function_entry_before_external {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function arguments continuation before world events external types result convention actual_arguments actual_cont after next:
  gateway_steps backend ge(gateway_live(Callstate(Internal function)arguments continuation before)world)events
    (gateway_live(Callstate(External external types result convention)actual_arguments actual_cont after)next)->
  exists prefix suffix memory current environment temporaries allocated,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge(gateway_live(Callstate(Internal function)arguments continuation before)world)prefix
      (gateway_live(Callstate(Internal function)arguments continuation memory)current) /\
    function_entry2 ge function arguments memory environment temporaries allocated /\
    gateway_steps backend ge(gateway_live(State function(fn_body function)continuation environment temporaries allocated)current)
      suffix(gateway_live(Callstate(External external types result convention)actual_arguments actual_cont after)next).
Proof.
  revert before world;induction events as[|event rest IH];intros before world RUN.
  - inversion RUN.
  - inversion RUN as[|first observed middle remaining last STEP TAIL];subst.
    destruct(gateway_function_call_step backend ge function arguments continuation before world event middle STEP)
      as[[environment[temporaries[allocated[EVENT[ENTRY TARGET]]]]]|
        [[changed[later[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + exists[],rest,before,world,environment,temporaries,allocated;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + destruct(IH changed later TAIL)as(prefix&suffix&memory&current&environment&temporaries&allocated&
        EVENTS&AMBIENT&PREFIX&ENTRY&SUFFIX).
      exists(gateway_ambient::prefix),suffix,memory,current,environment,temporaries,allocated.
      split;[cbn;congruence|]. split;[constructor;[reflexivity|exact AMBIENT]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;assumption.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
