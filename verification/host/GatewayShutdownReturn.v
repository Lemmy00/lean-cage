(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A failed half-close cannot return the original exchange's value. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFailurePaths GatewayIgnoredFailure
  GatewayExchangeTransport GatewayResponseReturn GatewayShutdownSource.
Import ListNotations.

Lemma actual_failed_response_entry {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  temporaries!_failed=Some(Vint(Int.neg Int.one))->
  gateway_failure_result backend ge(State f_host_exchange(exchange_transport_after 2)Kstop environment temporaries memory).
Proof.
  intro FAILED.
  eapply gateway_failure_edge with(target:=State f_host_exchange exchange_response_phase(Kseq(exchange_transport_after 3)Kstop)
    environment temporaries memory);[cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip(Kseq(exchange_transport_after 3)Kstop)
    environment temporaries memory).
  - cbn;tauto.
  - intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;WriteAll.expression|reflexivity].
  - eapply gateway_failure_edge with(target:=State f_host_exchange(exchange_transport_after 3)Kstop environment temporaries memory);
      [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    apply actual_failed_response_suffix;exact FAILED.
Qed.

Lemma actual_shutdown_failed_return {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  gateway_failure_result backend ge
    (Returnstate(Vint(Int.neg Int.one))(shutdown_cont environment temporaries)memory).
Proof.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip shutdown_after_call environment
    (PTree.set _t'34(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_failure_edge with(target:=State f_host_exchange shutdown_cast
    (Kseq exchange_shutdown_test(Kseq(exchange_transport_after 2)Kstop))environment
    (PTree.set _t'34(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  set(casted:=PTree.set _t'33(Vint Int.one)(PTree.set _t'34(Vint(Int.neg Int.one))temporaries)).
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip
    (Kseq exchange_shutdown_test(Kseq(exchange_transport_after 2)Kstop))environment casted memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_failure_edge with(target:=State f_host_exchange exchange_shutdown_test
    (Kseq(exchange_transport_after 2)Kstop)environment casted memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange shutdown_error_body
    (Kseq(exchange_transport_after 2)Kstop)environment casted memory);
    [cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value;unfold casted;WriteAll.expression|reflexivity]|].
  eapply gateway_failure_edge with(target:=State f_host_exchange shutdown_error_prefix
    (Kseq shutdown_error_mark(Kseq(exchange_transport_after 2)Kstop))environment casted memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange shutdown_error_load
    (Kseq shutdown_error_call(Kseq shutdown_error_mark(Kseq(exchange_transport_after 2)Kstop)))environment casted memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  apply gateway_failure_arbitrary_set;intro exception.
  set(loaded:=PTree.set _t'67 exception casted).
  eapply gateway_failure_edge with(target:=State f_host_exchange shutdown_error_call
    (Kseq shutdown_error_mark(Kseq(exchange_transport_after 2)Kstop))environment loaded memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply gateway_failure_ignored_call;intro ignored.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip
    (Kseq shutdown_error_mark(Kseq(exchange_transport_after 2)Kstop))environment loaded memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_failure_edge with(target:=State f_host_exchange shutdown_error_mark(Kseq(exchange_transport_after 2)Kstop)
    environment loaded memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip(Kseq(exchange_transport_after 2)Kstop)
    environment(PTree.set _failed(Vint(Int.neg Int.one))loaded)memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_failure_edge with(target:=State f_host_exchange(exchange_transport_after 2)Kstop
    environment(PTree.set _failed(Vint(Int.neg Int.one))loaded)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_failed_response_entry;apply PTree.gss.
Qed.

Theorem actual_successful_shutdown_return {World Event}(backend:gateway_backend World Event)ge
    environment temporaries before world events returned value after next:
  (returned=Vint Int.zero\/returned=Vint(Int.neg Int.one))->value<>Vnullptr->
  gateway_steps backend ge(gateway_live(Returnstate returned(shutdown_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->returned=Vint Int.zero.
Proof.
  intros[ZERO|FAILED]NONNULL RUN;[exact ZERO|subst returned;exfalso].
  apply NONNULL;exact(actual_shutdown_failed_return backend ge environment temporaries before before world events value after next RUN).
Qed.
