(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful original exchange derives its parser's non-NULL result. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFailurePaths GatewayNullReset
  GatewayExchangeTransport GatewayResponseReturn GatewayResponseParserSource.
Import ListNotations.

Lemma actual_null_result_cleanup {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  temporaries!_result=Some Vnullptr->
  gateway_failure_result backend ge(State f_host_exchange(exchange_transport_after 6)Kstop environment temporaries memory).
Proof.
  intro NULL.
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

Lemma actual_parser_null_return {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  gateway_failure_result backend ge(Returnstate Vnullptr(response_parser_cont environment temporaries)memory).
Proof.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip response_parser_after_call environment
    (PTree.set _t'44 Vnullptr temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  unfold response_parser_after_call.
  repeat response_denied_route.
  response_denied_set_as Vnullptr.
  repeat response_denied_route.
  response_denied_set_as Vnullptr.
  eapply gateway_failure_edge with(target:=State f_host_exchange(exchange_transport_after 6)Kstop environment
    (PTree.set _result Vnullptr(PTree.set _t'43 Vnullptr(PTree.set _t'44 Vnullptr temporaries)))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_null_result_cleanup;apply PTree.gss.
Qed.

Theorem actual_successful_parser_return {World Event}(backend:gateway_backend World Event)ge
    environment temporaries before world events parsed value after next:
  value<>Vnullptr->
  gateway_steps backend ge(gateway_live(Returnstate parsed(response_parser_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->parsed<>Vnullptr.
Proof.
  intros NONNULL RUN SAME;subst parsed;apply NONNULL.
  exact(actual_parser_null_return backend ge environment temporaries before before world events value after next RUN).
Qed.
