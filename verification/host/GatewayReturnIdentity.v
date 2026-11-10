(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual source returns preserve their selected pointer value. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Cop Clight.
Require Import Machine StoreSteps LocalAccess.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayReturns GatewayCallPath GatewayPure.

Theorem gateway_return_expression_identity {World Event}(backend:gateway_backend World Event)ge
    function expression continuation environment parameters before world selected events actual after next :
  call_cont continuation=Kstop ->
  (forall memory,expression_value ge environment parameters memory expression selected) ->
  (forall memory converted,sem_cast selected(typeof expression)(fn_return function)memory=Some converted ->converted=selected) ->
  gateway_steps backend ge(gateway_live(State function(Sreturn(Some expression))continuation environment parameters before)world)events
    (gateway_live(Returnstate actual Kstop after)next) ->actual=selected.
Proof.
  intros STOP EXPRESSION CAST;revert before world;induction events as[|observed rest IH];intros before world RUN.
  - inversion RUN.
  - inversion RUN as[|first event middle remaining last HEAD TAIL];subst.
    assert(INTERNAL:~gateway_at_primitive(State function(Sreturn(Some expression))continuation environment parameters before))
      by(cbn;tauto).
    destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
      as[[trace[target[EVENT[REAL TARGET]]]]|[[changed[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
      match goal with VALUE:eval_expr _ _ _ _ expression ?value|-_=>
        pose proof(proj2(EXPRESSION before)_ VALUE)as SAME;subst value end.
      match goal with CONVERSION:sem_cast selected _ _ _=Some ?converted|-_=>
        pose proof(CAST _ _ CONVERSION)as SAME;subst converted end.
      rewrite STOP in TAIL;eapply gateway_return_value_fixed;exact TAIL.
    + eapply IH;exact TAIL.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

Lemma gateway_pointer_cast_identity before source_type target_type value converted :
  (exists source,source_type=Tpointer source noattr) ->(exists target,target_type=Tpointer target noattr) ->
  sem_cast value source_type target_type before=Some converted ->converted=value.
Proof. intros[source SOURCE][target TARGET];subst source_type target_type;destruct value;cbn;intro SAME;inversion SAME;reflexivity. Qed.
