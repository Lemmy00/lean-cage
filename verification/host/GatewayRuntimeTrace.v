(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual coupled source scripts add no hidden primitive observations. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayReadonly GatewayFrames GatewayFramedRuntime.
Import ListNotations.

Lemma gateway_runtime_path_event {World Event}(backend:gateway_backend World Event)ge source world observed target value result :
  gateway_runtime_path_state backend ge value result(gateway_live source world) ->
  gateway_step backend ge(gateway_live source world)observed target ->
  observed=gateway_source E0 \/observed=gateway_ambient \/observed=gateway_lost.
Proof.
  intros[property[PROPERTY SCRIPT]]STEP;inversion STEP;subst;try solve[tauto].
  all:try solve[inversion SCRIPT;subst;cbn in *;try contradiction;
    match goal with INTERNAL:~gateway_at_primitive _|-_=>exfalso;apply INTERNAL;exact I end].
  inversion SCRIPT;subst.
  - match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
  - match goal with EDGES:forall memory world,property memory world->_|-_=>
      destruct(EDGES(memory_of source)world PROPERTY)as[changed[[IN[CANON UNIQUE]]POST]]end.
    rewrite gateway_memory_replace_identity in UNIQUE.
    match goal with REAL:step2 _ source _ _|-_=>destruct(UNIQUE _ _ REAL)as[TRACE SAME];subst end.
    left;reflexivity.
Qed.

Theorem gateway_runtime_path_return_events {World Event}(backend:gateway_backend World Event)ge
    property source value result before world events actual after next :
  property before world ->gateway_runtime_path backend ge property source value result ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Returnstate actual Kstop after)next) ->Forall gateway_quiet_event events.
Proof.
  intros PROPERTY SCRIPT RUN.
  assert(GOOD:gateway_runtime_path_state backend ge value result
    (gateway_live(gateway_replace_memory source before)world)).
  { exists property;split;[rewrite gateway_replace_memory_of;exact PROPERTY|apply gateway_runtime_replace;exact SCRIPT]. }
  remember(gateway_live(gateway_replace_memory source before)world)as initial eqn:INITIAL.
  remember(gateway_live(Returnstate actual Kstop after)next)as final eqn:FINAL.
  clear PROPERTY SCRIPT INITIAL before world source property.
  revert GOOD FINAL;induction RUN;intros GOOD FINAL;[constructor|].
  destruct first as[source world|memory world].
  - destruct(gateway_runtime_path_event backend ge source world observed middle value result GOOD H)
      as[SOURCE|[AMBIENT|LOST]].
    + constructor;[left;exact SOURCE|]. apply IHRUN;[eapply gateway_runtime_path_step;eassumption|exact FINAL].
    + constructor;[right;exact AMBIENT|]. apply IHRUN;[eapply gateway_runtime_path_step;eassumption|exact FINAL].
    + subst observed;inversion H;subst.
      destruct(gateway_dead_steps _ _ _ _ _ _ RUN)as[_ BAD];discriminate.
  - inversion H.
Qed.
