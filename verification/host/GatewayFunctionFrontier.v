(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: A selected later call exposes the actual preceding function
   entry. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayFunctionEntry.
Import ListNotations.

Theorem gateway_actual_function_entry_before_call {World Event}(backend:gateway_backend World Event)ge
    function arguments continuation before world events denied selected_arguments selected_cont selected_memory selected_world:
  denied<>Internal function->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal function)arguments continuation before)world)events
    (gateway_live(Callstate denied selected_arguments selected_cont selected_memory)selected_world)->
  exists prefix suffix called current environment temporaries allocated,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge(gateway_live(Callstate(Internal function)arguments continuation before)world)prefix
      (gateway_live(Callstate(Internal function)arguments continuation called)current) /\
    function_entry2 ge function arguments called environment temporaries allocated /\
    gateway_steps backend ge(gateway_live(State function(fn_body function)continuation environment temporaries allocated)current)
      suffix(gateway_live(Callstate denied selected_arguments selected_cont selected_memory)selected_world).
Proof.
  intros DIFFERENT;revert before world;induction events as[|observed rest IH];intros before world RUN.
  - inversion RUN;subst;contradiction.
  - inversion RUN;subst.
    match goal with STEP:gateway_step _ _ _ _ _|-_=>
      destruct(gateway_function_call_step _ _ _ _ _ _ _ _ _ STEP)
        as[[environment[temporaries[allocated[EVENT[ENTRY TARGET]]]]]|
          [[changed[next[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]]end;subst.
    + exists[],rest,before,world,environment,temporaries,allocated;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + match goal with TAIL:gateway_steps _ _
        (gateway_live(Callstate(Internal _) _ _ changed)next)_ _|-_=>
        destruct(IH changed next TAIL)as(prefix&suffix&called&current&environment&temporaries&allocated&
          EVENTS&AMBIENT&PREFIX&ENTRY&SUFFIX)end.
      exists(gateway_ambient::prefix),suffix,called,current,environment,temporaries,allocated.
      split;[cbn;congruence|]. split;[constructor;[reflexivity|exact AMBIENT]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;assumption.
    + match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
        destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.
