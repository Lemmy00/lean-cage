(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: A nonzero, non-retried EOF receive forces the real NULL result. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFailurePaths GatewayNullReset
  GatewayIgnoredFailure GatewayResponseReturn GatewayTrailingError GatewayExchangeTransport GatewayEOFSource
  GatewayEOFReadyReturn GatewayEOFReceiveSource GatewayEOFCountSource.
Import ListNotations.

Lemma actual_eof_count_error_failure {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  gateway_failure_result backend ge(State f_host_exchange exchange_eof_count_error
    (Kseq Sbreak exchange_eof_iteration_cont)environment temporaries memory).
Proof.
  unfold exchange_eof_count_error.
  repeat response_denied_route.
  trailing_error_arbitrary_set.
  repeat response_denied_route.
  trailing_error_ignore.
  repeat response_denied_route.
  trailing_error_ignore.
  repeat response_denied_route.
  response_denied_set_as Vnullptr.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sbreak exchange_eof_iteration_cont environment
    (PTree.set _result Vnullptr(PTree.set _t'58 assigned temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip exchange_eof_cont environment
    (PTree.set _result Vnullptr(PTree.set _t'58 assigned temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_break_loop1|].
  eapply gateway_failure_edge with(target:=State f_host_exchange exchange_cleanup_phase Kstop environment
    (PTree.set _result Vnullptr(PTree.set _t'58 assigned temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  intros before world events value after next RUN.
  eapply gateway_actual_reset_null with(protected:=_result);[|exact RUN].
  left;split;[repeat eexists;reflexivity|]. split;[WriteAll.lookup|].
  split;[reflexivity|left;exact(proj2(proj2(proj2 actual_exchange_transport_null_shapes)))].
Qed.

Lemma actual_eof_nonzero_count_failure {World Event}(backend:gateway_backend World Event)ge
    environment temporaries memory count:
  temporaries!_count=Some(Vlong count)->Int64.eq count Int64.zero=false->
  gateway_failure_result backend ge(State f_host_exchange exchange_eof_after_retry
    exchange_eof_iteration_cont environment temporaries memory).
Proof.
  intros COUNT NONZERO.
  eapply gateway_failure_edge with(target:=State f_host_exchange exchange_eof_count_test
    (Kseq Sbreak exchange_eof_iteration_cont)environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange exchange_eof_count_error
    (Kseq Sbreak exchange_eof_iteration_cont)environment temporaries memory);
    [cbn;tauto| |apply actual_eof_count_error_failure].
  intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true).
  - apply old_expression_value;eapply value_binary;[apply value_temp;exact COUNT|constructor|].
    change(Some(Val.of_bool(negb(Int64.eq count Int64.zero)))=Some(Vint Int.one)).
    rewrite NONZERO;reflexivity.
  - reflexivity.
Qed.

Lemma actual_eof_nonzero_skipped_failure {World Event}(backend:gateway_backend World Event)ge
    environment temporaries memory count:
  temporaries!_count=Some(Vlong count)->Int64.eq count Int64.zero=false->
  gateway_failure_result backend ge(State f_host_exchange Sskip
    (Kseq exchange_eof_after_retry exchange_eof_iteration_cont)environment temporaries memory).
Proof.
  intros COUNT NONZERO.
  eapply gateway_failure_edge with(target:=State f_host_exchange exchange_eof_after_retry
    exchange_eof_iteration_cont environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_eof_nonzero_count_failure with(count:=count);assumption.
Qed.
