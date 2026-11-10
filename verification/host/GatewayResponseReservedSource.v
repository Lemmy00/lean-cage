(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual successful magic/status guards select the reserved-word call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySourcePaths GatewayFramedRuntime
  GatewayExchangeTransport GatewayResponseCompareSource GatewayResponseGuards.
Import ListNotations.
Open Scope Z_scope.

Definition response_status_ok:=match response_status_test with Sifthenelse _ _ second=>second|_=>Sskip end.
Definition response_reserved_body:=match response_reserved_test with Sifthenelse _ _ second=>second|_=>Sskip end.
Definition response_reserved_call:=match response_reserved_body with Ssequence first _=>first|_=>Sskip end.
Definition response_reserved_cast:=match response_reserved_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_reserved_after_call:=Kseq response_reserved_cast(Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))).
Definition response_reserved_cont environment temporaries:=Kcall(Some _t'41)f_host_exchange environment temporaries response_reserved_after_call.
Definition response_reserved_temps temporaries:=PTree.set _t'39(Vint Int.zero)(PTree.set _t'38(Vint Int.zero)temporaries).
Definition response_reserved_arguments response:=[Vptr response(Ptrofs.repr 12);Vint(Int.repr 4)].

Lemma actual_response_reserved_call ge environment temporaries memory response:
  environment!_response=Some(response,tarray tuchar 24)->environment!_host_get64=None->
  gateway_function_binding ge _host_get64(Internal f_host_get64)->
  store_edge ge(State f_host_exchange response_reserved_call response_reserved_after_call environment temporaries memory)
    (Callstate(Internal f_host_get64)(response_reserved_arguments response)(response_reserved_cont environment temporaries)memory).
Proof.
  intros RESPONSE LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr response(Ptrofs.repr 12)).
    + eapply binary_expression_value.
      * eapply location_read_value;[apply local_location_value;exact RESPONSE|apply deref_loc_reference;reflexivity].
      * apply old_expression_value;constructor.
      * reflexivity.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint(Int.repr 4));
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_response_reserved_path {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory response status:
  environment!_response=Some(response,tarray tuchar 24)->environment!_host_get64=None->
  gateway_function_binding ge _host_get64(Internal f_host_get64)->
  temporaries!_status=Some(Vlong status)->Int64.unsigned status<=3->
  gateway_source_path backend ge(Internal f_host_get64)(response_reserved_arguments response)
    (response_reserved_cont environment(response_reserved_temps temporaries))property
    (Returnstate(Vint Int.zero)(response_compare_cont environment temporaries)memory)property.
Proof.
  intros RESPONSE LOCAL FUNCTION STATUS SMALL.
  eapply gateway_source_same with(target:=State f_host_exchange Sskip response_compare_after_call environment
    (PTree.set _t'38(Vint Int.zero)temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_source_same with(target:=State f_host_exchange response_status_test
    (Kseq response_reserved_test(Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))))environment
    (PTree.set _t'38(Vint Int.zero)temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange response_status_ok
    (Kseq response_reserved_test(Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))))environment
    (PTree.set _t'38(Vint Int.zero)temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;WriteAll.expression|reflexivity]|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip
    (Kseq response_reserved_test(Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))))environment
    (response_reserved_temps temporaries)memory);
    [exact CLOSED|cbn;tauto| |].
  { intros;apply certified_set_edge;eapply gateway_response_unsigned_within with(identifier:=_status)(word:=status)(limit:=3);
      [change(0<=3<=2147483647);lia|exact SMALL|rewrite PTree.gso by discriminate;exact STATUS]. }
  eapply gateway_source_same with(target:=State f_host_exchange response_reserved_test
    (Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop)))environment
    (response_reserved_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange response_reserved_body
    (Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop)))environment
    (response_reserved_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;unfold response_reserved_temps;WriteAll.expression|reflexivity]|].
  eapply gateway_source_same with(target:=State f_host_exchange response_reserved_call response_reserved_after_call environment
    (response_reserved_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=Callstate(Internal f_host_get64)(response_reserved_arguments response)
    (response_reserved_cont environment(response_reserved_temps temporaries))memory);
    [exact CLOSED|cbn;tauto|intros;eapply actual_response_reserved_call;eassumption|apply gateway_source_reached;intros;assumption].
Qed.
