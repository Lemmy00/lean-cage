(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An observed send failure cannot yield a successful exchange result. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayFailurePaths GatewayNullReset
  GatewayExchangeTransport.
Import ListNotations.
Open Scope Z_scope.

Section Denial.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv).
Variables(environment:env)(temporaries:temp_env)(memory:mem).
Hypothesis FAILED:temporaries!_failed=Some(Vint(Int.neg Int.one)).

Ltac denied_same sink:=eapply gateway_failure_edge with(target:=sink);[cbn;tauto| |].
Ltac denied_route:=lazymatch goal with
  | |-gateway_failure_result _ _ (State ?f ?body ?continuation ?locals ?temps ?m)=>
    let shape:=eval hnf in body in lazymatch shape with
    |Ssequence ?first ?rest=>
      denied_same(State f first(Kseq rest continuation)locals temps m);
        [intros;apply unchanged_store_edge,edge_seq|]
    |Sskip=>lazymatch continuation with
      Kseq ?rest ?outer=>denied_same(State f rest outer locals temps m);
        [intros;apply unchanged_store_edge,edge_skip_seq|]end
    end end.
Ltac denied_set_as value:=lazymatch goal with
  | |-gateway_failure_result _ _ (State ?f ?body ?continuation ?locals ?temps ?m)=>
    let shape:=eval hnf in body in lazymatch shape with
    |Sset ?identifier ?expression=>
      denied_same(State f Sskip continuation locals(PTree.set identifier value temps)m);
        [intros;apply certified_set_edge,old_expression_value;WriteAll.expression|]
    end end.
Ltac denied_branch choice value:=lazymatch goal with
  | |-gateway_failure_result _ _ (State ?f ?body ?continuation ?locals ?temps ?m)=>
    let shape:=eval hnf in body in lazymatch shape with
    |Sifthenelse ?test ?yes ?no=>
      denied_same(State f(if choice then yes else no)continuation locals temps m);
        [intros;apply certified_if_edge with(v:=value)(b:=choice);
          [apply old_expression_value;WriteAll.expression|reflexivity]|]
    end end.

Theorem actual_failed_exchange_suffix:
  gateway_failure_result backend ge
    (State f_host_exchange(exchange_transport_after 1)Kstop environment temporaries memory).
Proof.
  repeat denied_route.
  denied_branch false(Vint Int.zero).
  denied_set_as(Vint Int.zero).
  repeat denied_route.
  denied_branch false(Vint Int.zero).
  repeat denied_route.
  denied_branch false(Vint Int.zero).
  repeat denied_route.
  denied_set_as(Vlong Int64.zero).
  repeat denied_route.
  denied_branch false(Vint Int.zero).
  repeat denied_route.
  denied_branch true(Vint(Int.neg Int.one)).
  denied_set_as Vnullptr.
  repeat denied_route.
  denied_set_as Vnullptr.
  repeat denied_route.
  denied_branch false Vnullptr.
  denied_set_as(Vint Int.zero).
  repeat denied_route.
  denied_branch false(Vint Int.zero).
  repeat denied_route.
  denied_branch false Vnullptr.
  denied_route.
  intros before world events value after next RUN.
  eapply gateway_actual_reset_null with(protected:=_result);[|exact RUN].
  left;split;[repeat eexists;reflexivity|]. split.
  - WriteAll.lookup.
  - split;[reflexivity|left;exact(proj2(proj2(proj2 actual_exchange_transport_null_shapes)))].
Qed.
End Denial.
