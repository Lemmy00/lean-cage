(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Extract a real primitive occurrence, including all waiting and loss. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayReturns GatewayFrames GatewayPure.
Import ListNotations.

Definition gateway_pending_event {Event}(observed:gateway_event Event):Prop:=
  observed=gateway_ambient \/observed=gateway_blocked.

Theorem gateway_external_operation_of_run {World Event}(backend:gateway_backend World Event)ge
    external types result_type convention arguments before world events returned after final_world :
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory called_world changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\Forall gateway_pending_event prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)prefix
      (gateway_live(Callstate(External external types result_type convention)arguments Kstop memory)called_world) /\
    gateway_external backend external types result_type convention arguments memory called_world
      returned changed changed_world observed /\
    gateway_steps backend ge(gateway_live(Returnstate returned Kstop changed)changed_world)suffix
      (gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  revert before world;induction events as[|event rest IH];intros before world RUN.
  - inversion RUN.
  - inversion RUN;subst.
    match goal with STEP:gateway_step _ _ _ _ _|-_=>inversion STEP;subst end;cbn[gateway_replace_memory]in *.
    + contradiction.
    + match goal with TAIL:gateway_steps _ _ (gateway_live(Returnstate ?actual Kstop ?memory)?next)_ _|-_=>
        pose proof(gateway_return_value_fixed _ _ _ _ _ _ _ _ _ TAIL)as SAME;subst actual end.
      exists[],rest,before,world,after0,next,observed;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + match goal with TAIL:gateway_steps _ _
        (gateway_live(Callstate(External _ _ _ _) _ Kstop ?memory)?next)_ _|-_=>
        destruct(IH memory next TAIL)as[prefix[suffix[called[called_world[changed[changed_world
          [observed[EVENTS[PENDING[PREFIX[OPERATION SUFFIX]]]]]]]]]]]end.
      exists(gateway_ambient::prefix),suffix,called,called_world,changed,changed_world,observed.
      split;[cbn;congruence|]. split;[constructor;[left;reflexivity|exact PENDING]|]. split.
      * econstructor;[apply gateway_interleaved;eassumption|exact PREFIX].
      * split;assumption.
    + match goal with TAIL:gateway_steps _ _
        (gateway_live(Callstate(External _ _ _ _) _ Kstop ?memory)?next)_ _|-_=>
        destruct(IH memory next TAIL)as[prefix[suffix[called[called_world[changed[changed_world
          [observed[EVENTS[PENDING[PREFIX[OPERATION SUFFIX]]]]]]]]]]]end.
      exists(gateway_blocked::prefix),suffix,called,called_world,changed,changed_world,observed.
      split;[cbn;congruence|]. split;[constructor;[right;reflexivity|exact PENDING]|]. split.
      * econstructor;[apply gateway_waiting;exact I|exact PREFIX].
      * split;assumption.
    + match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
        destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
    + match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
        destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

(* A primitive's entry discipline is retained per ambient operation. It does not
   assert the primitive's return, a successful helper, or an independent trace. *)
Definition gateway_runtime_discipline {World Event}(backend:gateway_backend World Event)
    (ready:mem->World->Prop):Prop:=
  forall before world after next,ready before world ->
    gateway_interference backend before world after next ->ready after next.

Theorem gateway_pending_run_ready {World Event}(backend:gateway_backend World Event)ge ready
    (discipline:gateway_runtime_discipline backend ready)source before world events after next :
  ready before world ->Forall gateway_pending_event events ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(gateway_replace_memory source after)next) ->ready after next.
Proof.
  revert before world;induction events as[|event rest IH];intros before world READY PENDING RUN.
  - inversion RUN;subst.
    match goal with SAME:gateway_replace_memory _ _=gateway_replace_memory _ _|-_=>
      apply(f_equal memory_of)in SAME;destruct source;cbn in SAME;subst;exact READY end.
  - inversion PENDING;subst;inversion RUN;subst.
    match goal with KIND:gateway_pending_event event|-_=>destruct KIND as[SAME|SAME];subst event end.
    + match goal with STEP:gateway_step _ _ _ gateway_ambient _|-_=>inversion STEP;subst end.
      rewrite gateway_replace_memory_of in *.
      eapply IH;[eapply discipline;eassumption|eassumption|].
      rewrite gateway_memory_replace_twice in *;eassumption.
    + match goal with STEP:gateway_step _ _ _ gateway_blocked _|-_=>inversion STEP;subst end.
      eapply IH;eassumption.
Qed.
