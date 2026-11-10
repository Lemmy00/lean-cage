(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The response status call is reached from the same real read return. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySourcePaths GatewayFramedRuntime
  GatewayExchangeTransport GatewayResponseReturn GatewayExchangeSetup.
Import ListNotations.

Definition response_checks_body:=match exchange_response_checks with Sifthenelse _ first _=>first|_=>Sskip end.
Definition response_status_body:=match response_checks_body with Ssequence first _=>first|_=>Sskip end.
Definition response_after_status:=match response_checks_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_status_call:=match response_status_body with Ssequence first _=>first|_=>Sskip end.
Definition response_status_bind:=match response_status_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_header_temps temporaries:=PTree.set _status(Vlong Int64.zero)
  (PTree.set _failed(Vint Int.zero)(PTree.set _t'35(Vint Int.zero)temporaries)).
Definition response_status_after_call:=Kseq response_status_bind(Kseq response_after_status(Kseq(exchange_transport_after 5)Kstop)).
Definition response_status_cont environment temporaries:=Kcall(Some _t'36)f_host_exchange environment temporaries response_status_after_call.
Definition response_status_arguments response:=[Vptr response(Ptrofs.repr 8);Vint(Int.repr 4)].

Lemma actual_response_status_call ge environment temporaries memory response:
  environment!_response=Some(response,tarray tuchar 24)->environment!_host_get64=None->
  gateway_function_binding ge _host_get64(Internal f_host_get64)->
  store_edge ge(State f_host_exchange response_status_call response_status_after_call environment temporaries memory)
    (Callstate(Internal f_host_get64)(response_status_arguments response)(response_status_cont environment temporaries)memory).
Proof.
  intros RESPONSE LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr response(Ptrofs.repr 8)).
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

Section StatusPath.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (property:mem->World->Prop)(CLOSED:gateway_ambient_closed backend property).
Variables(environment:env)(temporaries:temp_env)(memory:mem)(response:block).
Hypotheses(RESPONSE:environment!_response=Some(response,tarray tuchar 24))
  (LOCAL:environment!_host_get64=None)(FUNCTION:gateway_function_binding ge _host_get64(Internal f_host_get64)).

Local Ltac status_same sink:=eapply gateway_source_same with(target:=sink);[exact CLOSED|cbn;tauto| |].

Theorem actual_response_status_path:
  gateway_source_path backend ge(Internal f_host_get64)(response_status_arguments response)
    (response_status_cont environment(response_header_temps temporaries))property
    (Returnstate(Vint Int.zero)(response_transfer_cont environment temporaries)memory)property.
Proof.
  status_same(State f_host_exchange Sskip(Kseq response_transfer_bind(Kseq(exchange_transport_after 3)Kstop))environment
    (PTree.set _t'35(Vint Int.zero)temporaries)memory);
    [intros;apply unchanged_store_edge,edge_returnstate|].
  status_same(State f_host_exchange response_transfer_bind(Kseq(exchange_transport_after 3)Kstop)environment
    (PTree.set _t'35(Vint Int.zero)temporaries)memory);
    [intros;apply unchanged_store_edge,edge_skip_seq|].
  status_same(State f_host_exchange Sskip(Kseq(exchange_transport_after 3)Kstop)environment
    (PTree.set _failed(Vint Int.zero)(PTree.set _t'35(Vint Int.zero)temporaries))memory);
    [intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  status_same(State f_host_exchange(exchange_transport_after 3)Kstop environment
    (PTree.set _failed(Vint Int.zero)(PTree.set _t'35(Vint Int.zero)temporaries))memory);
    [intros;apply unchanged_store_edge,edge_skip_seq|].
  status_same(State f_host_exchange exchange_status_phase(Kseq(exchange_transport_after 4)Kstop)environment
    (PTree.set _failed(Vint Int.zero)(PTree.set _t'35(Vint Int.zero)temporaries))memory);
    [intros;apply unchanged_store_edge,edge_seq|].
  status_same(State f_host_exchange Sskip(Kseq(exchange_transport_after 4)Kstop)environment(response_header_temps temporaries)memory);
    [intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  status_same(State f_host_exchange(exchange_transport_after 4)Kstop environment(response_header_temps temporaries)memory);
    [intros;apply unchanged_store_edge,edge_skip_seq|].
  status_same(State f_host_exchange exchange_response_checks(Kseq(exchange_transport_after 5)Kstop)environment(response_header_temps temporaries)memory);
    [intros;apply unchanged_store_edge,edge_seq|].
  status_same(State f_host_exchange response_checks_body(Kseq(exchange_transport_after 5)Kstop)environment(response_header_temps temporaries)memory).
  - intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value;unfold response_header_temps;WriteAll.expression|reflexivity].
  - status_same(State f_host_exchange response_status_body(Kseq response_after_status(Kseq(exchange_transport_after 5)Kstop))
      environment(response_header_temps temporaries)memory);
      [intros;apply unchanged_store_edge,edge_seq|].
    status_same(State f_host_exchange response_status_call response_status_after_call environment(response_header_temps temporaries)memory);
      [intros;apply unchanged_store_edge,edge_seq|].
    status_same(Callstate(Internal f_host_get64)(response_status_arguments response)
      (response_status_cont environment(response_header_temps temporaries))memory).
    + intros;eapply actual_response_status_call;eassumption.
    + apply gateway_source_reached;intros;assumption.
Qed.
End StatusPath.
