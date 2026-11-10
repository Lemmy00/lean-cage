(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real request half-close loads the same private stream endpoint. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayExchangeABI GatewayExchangeTransport
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayStreamInterface GatewayStreamLayout.
Import ListNotations.
Open Scope Z_scope.

Definition shutdown_body:=match exchange_shutdown_select with Sifthenelse _ first _=>first|_=>Sskip end.
Definition shutdown_prefix:=match shutdown_body with Ssequence first _=>first|_=>Sskip end.
Definition shutdown_load:=match shutdown_prefix with Ssequence first _=>first|_=>Sskip end.
Definition shutdown_call:=match shutdown_prefix with Ssequence _ rest=>rest|_=>Sskip end.
Definition shutdown_cast:=match shutdown_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition shutdown_error_body:=match exchange_shutdown_test with Sifthenelse _ first _=>first|_=>Sskip end.
Definition shutdown_error_prefix:=match shutdown_error_body with Ssequence first _=>first|_=>Sskip end.
Definition shutdown_error_load:=match shutdown_error_prefix with Ssequence first _=>first|_=>Sskip end.
Definition shutdown_error_call:=match shutdown_error_prefix with Ssequence _ rest=>rest|_=>Sskip end.
Definition shutdown_error_mark:=match shutdown_error_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition shutdown_after_call:=Kseq shutdown_cast(Kseq exchange_shutdown_test(Kseq(exchange_transport_after 2)Kstop)).
Definition shutdown_temps descriptor temporaries:=PTree.set _t'68(Vint descriptor)temporaries.
Definition shutdown_cont environment temporaries:=Kcall(Some _t'34)f_host_exchange environment temporaries shutdown_after_call.

Lemma actual_local_stream_descriptor ge environment temporaries memory stream initial:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->stream_member_layout ge _descriptor 0->
  gateway_stream_memory memory stream Ptrofs.zero initial->
  expression_value ge environment temporaries memory
    (Efield(Evar _stream(Tstruct _host_stream noattr))_descriptor tint)(Vint(stream_descriptor initial)).
Proof.
  intros STREAM[composite[LAYOUT MEMBER]]CELLS.
  eapply location_read_value with(b:=stream)(ofs:=Ptrofs.add Ptrofs.zero(Ptrofs.repr 0)).
  - eapply struct_location_value with(id:=_host_stream)(co:=composite)(att:=noattr)(delta:=0);
      [eapply location_read_value;[apply local_location_value;exact STREAM|apply deref_loc_copy;reflexivity]|
        reflexivity|exact LAYOUT|exact MEMBER].
  - eapply deref_loc_value;[reflexivity|exact(proj1 CELLS)].
Qed.

Lemma actual_shutdown_call ge environment temporaries memory descriptor:
  temporaries!_t'68=Some(Vint descriptor)->environment!_shutdown=None->
  gateway_function_binding ge _shutdown gateway_shutdown_definition->
  store_edge ge(State f_host_exchange shutdown_call shutdown_after_call environment temporaries memory)
    (Callstate gateway_shutdown_definition[Vint descriptor;Vint Int.one](shutdown_cont environment temporaries)memory).
Proof.
  intros DESCRIPTOR LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint descriptor).
    + apply old_expression_value,value_temp;exact DESCRIPTOR.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint Int.one);
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_shutdown_prefix {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory stream initial:
  temporaries!_failed=Some(Vint Int.zero)->environment!_stream=Some(stream,Tstruct _host_stream noattr)->
  stream_member_layout ge _descriptor 0->environment!_shutdown=None->
  gateway_function_binding ge _shutdown gateway_shutdown_definition->
  (forall memory world,property memory world->gateway_stream_memory memory stream Ptrofs.zero initial)->
  gateway_memory_prefix backend ge
    (Callstate gateway_shutdown_definition[Vint(stream_descriptor initial);Vint Int.one]
      (shutdown_cont environment(shutdown_temps(stream_descriptor initial)temporaries))memory)property property
    (State f_host_exchange(exchange_transport_after 1)Kstop environment temporaries memory).
Proof.
  intros FAILED STREAM LAYOUT LOCAL FUNCTION CELLS.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_shutdown_phase
    (Kseq(exchange_transport_after 2)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_shutdown_select
    (Kseq exchange_shutdown_test(Kseq(exchange_transport_after 2)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange shutdown_body
    (Kseq exchange_shutdown_test(Kseq(exchange_transport_after 2)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  { intros before world READY;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value;WriteAll.expression|reflexivity]. }
  eapply gateway_memory_same with(following:=State f_host_exchange shutdown_prefix shutdown_after_call environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange shutdown_load(Kseq shutdown_call shutdown_after_call)
    environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq shutdown_call shutdown_after_call)
    environment(shutdown_temps(stream_descriptor initial)temporaries)memory);
    [exact CLOSED|cbn;tauto| |].
  { intros before world READY;apply certified_set_edge;eapply actual_local_stream_descriptor;
      [exact STREAM|exact LAYOUT|exact(CELLS before world READY)]. }
  eapply gateway_memory_same with(following:=State f_host_exchange shutdown_call shutdown_after_call
    environment(shutdown_temps(stream_descriptor initial)temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=Callstate gateway_shutdown_definition[Vint(stream_descriptor initial);Vint Int.one]
    (shutdown_cont environment(shutdown_temps(stream_descriptor initial)temporaries))memory);
    [exact CLOSED|cbn;tauto|intros;eapply actual_shutdown_call;[apply PTree.gss|exact LOCAL|exact FUNCTION]|apply gateway_memory_identity].
Qed.
