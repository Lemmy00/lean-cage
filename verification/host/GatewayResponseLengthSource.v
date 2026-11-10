(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The second header word comes from the original length-call source. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySourcePaths GatewayFramedRuntime
  GatewayExchangeTransport GatewayResponseStatusSource.
Import ListNotations.

Definition response_length_body:=match response_after_status with Ssequence first _=>first|_=>Sskip end.
Definition response_after_length:=match response_after_status with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_length_call:=match response_length_body with Ssequence first _=>first|_=>Sskip end.
Definition response_length_store:=match response_length_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_length_temps(status:val)temporaries:=PTree.set _status status(PTree.set _t'36 status temporaries).
Definition response_length_after_call:=Kseq response_length_store(Kseq response_after_length(Kseq(exchange_transport_after 5)Kstop)).
Definition response_length_cont environment temporaries:=Kcall(Some _t'37)f_host_exchange environment temporaries response_length_after_call.
Definition response_length_arguments response:=[Vptr response(Ptrofs.repr 16);Vint(Int.repr 8)].

Lemma actual_response_length_call ge environment temporaries memory response:
  environment!_response=Some(response,tarray tuchar 24)->environment!_host_get64=None->
  gateway_function_binding ge _host_get64(Internal f_host_get64)->
  store_edge ge(State f_host_exchange response_length_call response_length_after_call environment temporaries memory)
    (Callstate(Internal f_host_get64)(response_length_arguments response)(response_length_cont environment temporaries)memory).
Proof.
  intros RESPONSE LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr response(Ptrofs.repr 16)).
    + eapply binary_expression_value.
      * eapply location_read_value;[apply local_location_value;exact RESPONSE|apply deref_loc_reference;reflexivity].
      * apply old_expression_value;constructor.
      * reflexivity.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint(Int.repr 8));
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_response_length_path {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory response status:
  environment!_response=Some(response,tarray tuchar 24)->environment!_host_get64=None->
  gateway_function_binding ge _host_get64(Internal f_host_get64)->
  gateway_source_path backend ge(Internal f_host_get64)(response_length_arguments response)
    (response_length_cont environment(response_length_temps status temporaries))property
    (Returnstate status(response_status_cont environment temporaries)memory)property.
Proof.
  intros RESPONSE LOCAL FUNCTION.
  eapply gateway_source_same with(target:=State f_host_exchange Sskip response_status_after_call environment(PTree.set _t'36 status temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_source_same with(target:=State f_host_exchange response_status_bind
    (Kseq response_after_status(Kseq(exchange_transport_after 5)Kstop))environment(PTree.set _t'36 status temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip
    (Kseq response_after_status(Kseq(exchange_transport_after 5)Kstop))environment(response_length_temps status temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_source_same with(target:=State f_host_exchange response_after_status(Kseq(exchange_transport_after 5)Kstop)
    environment(response_length_temps status temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange response_length_body(Kseq response_after_length(Kseq(exchange_transport_after 5)Kstop))
    environment(response_length_temps status temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange response_length_call response_length_after_call
    environment(response_length_temps status temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=Callstate(Internal f_host_get64)(response_length_arguments response)
    (response_length_cont environment(response_length_temps status temporaries))memory);
    [exact CLOSED|cbn;tauto|intros;eapply actual_response_length_call;eassumption|apply gateway_source_reached;intros;assumption].
Qed.
