(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual response caller derives its nested transfer return. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayReturns GatewayFailurePaths
  GatewayNullReset GatewayReturnTypes GatewayExchangeTransport GatewayExchangeDenied.
Import ListNotations.

Definition response_transfer_body:=match exchange_response_phase with Sifthenelse _ first _=>first|_=>Sskip end.
Definition response_transfer_call:=match response_transfer_body with Ssequence first _=>first|_=>Sskip end.
Definition response_transfer_bind:=match response_transfer_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_transfer_cont environment temporaries:=Kcall(Some _t'35)f_host_exchange environment temporaries
  (Kseq response_transfer_bind(Kseq(exchange_transport_after 3)Kstop)).

Ltac response_denied_same sink:=eapply gateway_failure_edge with(target:=sink);[cbn;tauto| |].
Ltac response_denied_route:=lazymatch goal with
  | |-gateway_failure_result _ _ (State ?f ?body ?continuation ?locals ?temps ?m)=>
    let shape:=eval hnf in body in lazymatch shape with
    |Ssequence ?first ?rest=>
      response_denied_same(State f first(Kseq rest continuation)locals temps m);
        [intros;apply unchanged_store_edge,edge_seq|]
    |Sskip=>lazymatch continuation with
      Kseq ?rest ?outer=>response_denied_same(State f rest outer locals temps m);
        [intros;apply unchanged_store_edge,edge_skip_seq|]end
    end end.
Ltac response_denied_set_as value:=lazymatch goal with
  | |-gateway_failure_result _ _ (State ?f ?body ?continuation ?locals ?temps ?m)=>
    let shape:=eval hnf in body in lazymatch shape with
    |Sset ?identifier ?expression=>
      response_denied_same(State f Sskip continuation locals(PTree.set identifier value temps)m);
        [intros;apply certified_set_edge,old_expression_value;WriteAll.expression|]
    end end.
Ltac response_denied_branch choice value:=lazymatch goal with
  | |-gateway_failure_result _ _ (State ?f ?body ?continuation ?locals ?temps ?m)=>
    let shape:=eval hnf in body in lazymatch shape with
    |Sifthenelse ?test ?yes ?no=>
      response_denied_same(State f(if choice then yes else no)continuation locals temps m);
        [intros;apply certified_if_edge with(v:=value)(b:=choice);
          [apply old_expression_value;WriteAll.expression|reflexivity]|]
    end end.


Lemma actual_failed_response_suffix {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  temporaries!_failed=Some(Vint(Int.neg Int.one))->
  gateway_failure_result backend ge(State f_host_exchange(exchange_transport_after 3)Kstop environment temporaries memory).
Proof.
  intro FAILED.
  repeat response_denied_route.
  response_denied_set_as(Vlong Int64.zero).
  repeat response_denied_route.
  response_denied_branch false(Vint Int.zero).
  repeat response_denied_route.
  response_denied_branch true(Vint(Int.neg Int.one)).
  response_denied_set_as Vnullptr.
  repeat response_denied_route.
  response_denied_set_as Vnullptr.
  repeat response_denied_route.
  response_denied_branch false Vnullptr.
  response_denied_set_as(Vint Int.zero).
  repeat response_denied_route.
  response_denied_branch false(Vint Int.zero).
  repeat response_denied_route.
  response_denied_branch false Vnullptr.
  response_denied_route.
  intros before world events value after next RUN.
  eapply gateway_actual_reset_null with(protected:=_result);[|exact RUN].
  left;split;[repeat eexists;reflexivity|]. split.
  - WriteAll.lookup.
  - split;[reflexivity|left;exact(proj2(proj2(proj2 actual_exchange_transport_null_shapes)))].
Qed.

Lemma actual_response_failed_return {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  gateway_failure_result backend ge
    (Returnstate(Vint(Int.neg Int.one))(response_transfer_cont environment temporaries)memory).
Proof.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip
    (Kseq response_transfer_bind(Kseq(exchange_transport_after 3)Kstop))environment
    (PTree.set _t'35(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_failure_edge with(target:=State f_host_exchange response_transfer_bind(Kseq(exchange_transport_after 3)Kstop)
    environment(PTree.set _t'35(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip(Kseq(exchange_transport_after 3)Kstop)environment
    (PTree.set _failed(Vint(Int.neg Int.one))(PTree.set _t'35(Vint(Int.neg Int.one))temporaries))memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_failure_edge with(target:=State f_host_exchange(exchange_transport_after 3)Kstop environment
    (PTree.set _failed(Vint(Int.neg Int.one))(PTree.set _t'35(Vint(Int.neg Int.one))temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_failed_response_suffix;apply PTree.gss.
Qed.

Lemma actual_response_undefined_return ge environment temporaries memory:
  gateway_blocked_path ge(Returnstate Vundef(response_transfer_cont environment temporaries)memory).
Proof.
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip
    (Kseq response_transfer_bind(Kseq(exchange_transport_after 3)Kstop))environment(PTree.set _t'35 Vundef temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_blocked_next with(next:=State f_host_exchange response_transfer_bind(Kseq(exchange_transport_after 3)Kstop)
    environment(PTree.set _t'35 Vundef temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip(Kseq(exchange_transport_after 3)Kstop)environment
    (PTree.set _failed Vundef(PTree.set _t'35 Vundef temporaries))memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_blocked_next with(next:=State f_host_exchange(exchange_transport_after 3)Kstop environment
    (PTree.set _failed Vundef(PTree.set _t'35 Vundef temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange exchange_status_phase(Kseq(exchange_transport_after 4)Kstop)
    environment(PTree.set _failed Vundef(PTree.set _t'35 Vundef temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip(Kseq(exchange_transport_after 4)Kstop)
    environment(PTree.set _status(Vlong Int64.zero)(PTree.set _failed Vundef(PTree.set _t'35 Vundef temporaries)))memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_blocked_next with(next:=State f_host_exchange(exchange_transport_after 4)Kstop
    environment(PTree.set _status(Vlong Int64.zero)(PTree.set _failed Vundef(PTree.set _t'35 Vundef temporaries)))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange exchange_response_checks(Kseq(exchange_transport_after 5)Kstop)
    environment(PTree.set _status(Vlong Int64.zero)(PTree.set _failed Vundef(PTree.set _t'35 Vundef temporaries)))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  apply gateway_blocked_at.
  - cbn;tauto.
  - intros;discriminate.
  - intros available trace target STEP;inversion STEP;subst;
      try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
    all:match goal with VALUE:eval_expr _ _ _ _(Eunop Onotbool _ _)_|-_=>inversion VALUE;subst end.
    all:try match goal with BAD:eval_lvalue _ _ _ _(Eunop _ _ _)_ _ _|-_=>inversion BAD end.
    all:match goal with VALUE:eval_expr _ _ _ _(Etempvar ?identifier ?ty)_|-_=>
      assert(LOOK:(PTree.set _status(Vlong Int64.zero)(PTree.set _failed Vundef(PTree.set _t'35 Vundef temporaries)))!identifier=Some Vundef)
        by WriteAll.lookup;
      pose proof(evaluated_unique _ _ _ _ _ _(value_temp _ _ _ _ identifier ty Vundef LOOK)_ VALUE)as SAME;subst end.
    all:discriminate.
Qed.

Theorem actual_successful_response_return {World Event}(backend:gateway_backend World Event)ge
    environment temporaries before world events returned value after next:
  gateway_int_return_value returned->value<>Vnullptr->
  gateway_steps backend ge(gateway_live(Returnstate returned(response_transfer_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->returned=Vint Int.zero.
Proof.
  intros[UNDEFINED|[ZERO|FAILED]]NONNULL RUN;[subst returned|exact ZERO|subst returned].
  - exfalso;eapply gateway_blocked_cannot_return;[apply actual_response_undefined_return|exact RUN].
  - exfalso;apply NONNULL;exact(actual_response_failed_return backend ge environment temporaries before
      before world events value after next RUN).
Qed.
