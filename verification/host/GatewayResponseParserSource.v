(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Validated real header guards reach the actual bounded parser call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayPrefix GatewaySourcePaths GatewayFramedRuntime
  GatewayStreamInterface GatewayStreamLayout GatewayExchangeTransport GatewayResponseReservedSource GatewayResponseCompareSource GatewayResponseGuards.
Import ListNotations.
Open Scope Z_scope.

Definition response_size_ok:=match response_size_test with Sifthenelse _ _ second=>second|_=>Sskip end.
Definition response_remaining_load:=match response_size_ok with Ssequence first _=>first|_=>Sskip end.
Definition response_remaining_test:=match response_size_ok with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_parser_body:=match exchange_result_select with Sifthenelse _ _ second=>second|_=>Sskip end.
Definition response_parser_call:=match response_parser_body with Ssequence first _=>first|_=>Sskip end.
Definition response_parser_bind:=match response_parser_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_parser_after_call:=Kseq response_parser_bind(Kseq exchange_result_bind(Kseq(exchange_transport_after 6)Kstop)).
Definition response_parser_cont environment temporaries:=Kcall(Some _t'44)f_host_exchange environment temporaries response_parser_after_call.
Definition response_parser_arguments stream:=[Vptr stream Ptrofs.zero;Vint(Int.repr 72)].
Definition response_parser_temps remaining temporaries:=PTree.set _t'42(Vint Int.zero)(PTree.set _t'66(Vlong remaining)
  (PTree.set _t'40(Vint Int.zero)(PTree.set _t'41(Vlong Int64.zero)temporaries))).

Lemma actual_local_response_remaining ge environment temporaries memory stream initial:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->stream_member_layout ge _remaining 24->
  gateway_stream_memory memory stream Ptrofs.zero initial->
  expression_value ge environment temporaries memory
    (Efield(Evar _stream(Tstruct _host_stream noattr))_remaining tulong)(Vlong(stream_remaining initial)).
Proof.
  intros STREAM[composite[LAYOUT MEMBER]]CELLS.
  eapply location_read_value with(b:=stream)(ofs:=Ptrofs.add Ptrofs.zero(Ptrofs.repr 24)).
  - eapply struct_location_value with(id:=_host_stream)(co:=composite)(att:=noattr)(delta:=24).
    + eapply location_read_value;[apply local_location_value;exact STREAM|apply deref_loc_copy;reflexivity].
    + reflexivity.
    + exact LAYOUT.
    + exact MEMBER.
  - eapply deref_loc_value;[reflexivity|exact(proj1(proj2(proj2(proj2(proj2(proj2 CELLS))))))].
Qed.

Lemma actual_response_parser_call ge environment temporaries memory stream:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_host_value=None->
  gateway_function_binding ge _host_value(Internal f_host_value)->
  store_edge ge(State f_host_exchange response_parser_call response_parser_after_call environment temporaries memory)
    (Callstate(Internal f_host_value)(response_parser_arguments stream)(response_parser_cont environment temporaries)memory).
Proof.
  intros STREAM LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr stream Ptrofs.zero).
    + apply local_address_expression;exact STREAM.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint(Int.repr 72));
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_response_parser_path {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory stream initial:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_host_value=None->
  gateway_function_binding ge _host_value(Internal f_host_value)->stream_member_layout ge _remaining 24->
  temporaries!_failed=Some(Vint Int.zero)->Int64.unsigned(stream_remaining initial)<=536870912->
  (forall memory world,property memory world->gateway_stream_memory memory stream Ptrofs.zero initial)->
  gateway_source_path backend ge(Internal f_host_value)(response_parser_arguments stream)
    (response_parser_cont environment(response_parser_temps(stream_remaining initial)temporaries))property
    (Returnstate(Vlong Int64.zero)(response_reserved_cont environment temporaries)memory)property.
Proof.
  intros STREAM LOCAL FUNCTION LAYOUT FAILED SMALL CELLS.
  set(returned:=PTree.set _t'41(Vlong Int64.zero)temporaries).
  set(casted:=PTree.set _t'40(Vint Int.zero)returned).
  set(loaded:=PTree.set _t'66(Vlong(stream_remaining initial))casted).
  set(checked:=response_parser_temps(stream_remaining initial)temporaries).
  eapply gateway_source_same with(target:=State f_host_exchange Sskip response_reserved_after_call environment returned memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_source_same with(target:=State f_host_exchange response_reserved_cast
    (Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop)))environment returned memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip
    (Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop)))environment casted memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value;unfold returned;WriteAll.expression|].
  eapply gateway_source_same with(target:=State f_host_exchange response_size_test
    (Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))environment casted memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange response_size_ok
    (Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))environment casted memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;unfold casted;WriteAll.expression|reflexivity]|].
  eapply gateway_source_same with(target:=State f_host_exchange response_remaining_load
    (Kseq response_remaining_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop)))environment casted memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip
    (Kseq response_remaining_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop)))environment loaded memory);
    [exact CLOSED|cbn;tauto| |].
  { intros before world READY;apply certified_set_edge;eapply actual_local_response_remaining;[exact STREAM|exact LAYOUT|exact(CELLS before world READY)]. }
  eapply gateway_source_same with(target:=State f_host_exchange response_remaining_test
    (Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))environment loaded memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip
    (Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))environment checked memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_set_edge;eapply gateway_response_unsigned_within with(identifier:=_t'66)(word:=stream_remaining initial)(limit:=536870912);
      [change(0<=536870912<=2147483647);lia|exact SMALL|unfold loaded;apply PTree.gss]|].
  eapply gateway_source_same with(target:=State f_host_exchange response_bounds_test(Kseq(exchange_transport_after 5)Kstop)
    environment checked memory);[exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip(Kseq(exchange_transport_after 5)Kstop)environment checked memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;unfold checked,response_parser_temps;WriteAll.expression|reflexivity]|].
  eapply gateway_source_same with(target:=State f_host_exchange(exchange_transport_after 5)Kstop environment checked memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_result_phase(Kseq(exchange_transport_after 6)Kstop)environment checked memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_result_select
    (Kseq exchange_result_bind(Kseq(exchange_transport_after 6)Kstop))environment checked memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange response_parser_body
    (Kseq exchange_result_bind(Kseq(exchange_transport_after 6)Kstop))environment checked memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;unfold checked,response_parser_temps,loaded,casted,returned;WriteAll.expression|reflexivity]|].
  eapply gateway_source_same with(target:=State f_host_exchange response_parser_call response_parser_after_call environment checked memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=Callstate(Internal f_host_value)(response_parser_arguments stream)(response_parser_cont environment checked)memory);
    [exact CLOSED|cbn;tauto|intros;eapply actual_response_parser_call;eassumption|apply gateway_source_reached;intros;assumption].
Qed.
