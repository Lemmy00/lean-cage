(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: A later selected call retains the same actual caller return edge. *)
From Stdlib Require Import List.
From compcert Require Import Maps AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayCallPath GatewayFrames GatewayOperations GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_return_before_call {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)value destination function environment temporaries continuation
    before world events definition arguments selected_cont after next:
  property before world->
  gateway_steps backend ge
    (gateway_live(Returnstate value(Kcall destination function environment temporaries continuation)before)world)events
    (gateway_live(Callstate definition arguments selected_cont after)next)->
  exists pending rest memory current,
    events=pending++gateway_source E0::rest /\Forall(fun event=>event=gateway_ambient)pending /\
    gateway_steps backend ge
      (gateway_live(Returnstate value(Kcall destination function environment temporaries continuation)before)world)pending
      (gateway_live(Returnstate value(Kcall destination function environment temporaries continuation)memory)current) /\
    property memory current /\
    gateway_steps backend ge
      (gateway_live(State function Sskip continuation environment(set_opttemp destination value temporaries)memory)current)rest
      (gateway_live(Callstate definition arguments selected_cont after)next).
Proof.
  revert before world;induction events as[|event rest IH];intros before world READY RUN.
  - inversion RUN.
  - inversion RUN as[|first observed middle remaining last STEP TAIL];subst.
    destruct(gateway_nonprimitive_step backend ge
      (Returnstate value(Kcall destination function environment temporaries continuation)before)world event middle
      ltac:(cbn;tauto)STEP)
      as[[trace[actual[EVENT[REAL TARGET]]]]|
        [[changed[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion REAL;subst;exists[],rest,before,world;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + destruct(IH changed current(CLOSED _ _ _ _ READY INTERFERENCE)TAIL)
        as(pending&suffix&memory&owner&EVENTS&AMBIENT&PREFIX&FINAL&SUFFIX).
      exists(gateway_ambient::pending),suffix,memory,owner;split;[cbn;congruence|].
      split;[constructor;[reflexivity|exact AMBIENT]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;assumption.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
