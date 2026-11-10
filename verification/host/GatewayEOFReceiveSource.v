(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: EOF readiness precedes the same socket's one-byte receive. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayRuntimeABI GatewaySourcePaths GatewayFramedRuntime
  GatewayPrefix GatewayExchangeTransport GatewayStreamInterface GatewayStreamLayout GatewayShutdownSource GatewayEOFSource.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_eof_receive_sequence:=match exchange_eof_after_ready with Ssequence first _=>first|_=>Sskip end.
Definition exchange_eof_after_receive:=match exchange_eof_after_ready with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_eof_receive_prefix:=match exchange_eof_receive_sequence with Ssequence first _=>first|_=>Sskip end.
Definition exchange_eof_receive_bind:=match exchange_eof_receive_sequence with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_eof_receive_load:=match exchange_eof_receive_prefix with Ssequence first _=>first|_=>Sskip end.
Definition exchange_eof_receive_call:=match exchange_eof_receive_prefix with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_eof_receive_after:=Kseq exchange_eof_receive_bind(Kseq exchange_eof_after_receive exchange_eof_iteration_cont).
Definition exchange_eof_receive_cont environment temporaries:=Kcall(Some _t'47)f_host_exchange environment temporaries exchange_eof_receive_after.
Definition exchange_eof_receive_arguments descriptor extra:=
  [Vint descriptor;Vptr extra Ptrofs.zero;Vlong Int64.one;Vint Int.zero].
Definition exchange_eof_ready_temps(temporaries:temp_env):=PTree.set _t'46(Vint Int.zero)temporaries.
Definition exchange_eof_receive_temps descriptor temporaries:=PTree.set _t'62(Vint descriptor)(exchange_eof_ready_temps temporaries).

Theorem actual_eof_receive_call ge environment temporaries memory extra descriptor:
  environment!_extra=Some(extra,tuchar)->environment!_recv=None->
  gateway_function_binding ge _recv gateway_receive_definition->temporaries!_t'62=Some(Vint descriptor)->
  store_edge ge(State f_host_exchange exchange_eof_receive_call exchange_eof_receive_after environment temporaries memory)
    (Callstate gateway_receive_definition(exchange_eof_receive_arguments descriptor extra)(exchange_eof_receive_cont environment temporaries)memory).
Proof.
  intros EXTRA LOCAL[symbol[SYMBOL FUNCTION]]DESCRIPTOR.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint descriptor).
    + apply old_expression_value,value_temp;exact DESCRIPTOR.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vptr extra Ptrofs.zero).
      * apply local_address_expression;exact EXTRA.
      * reflexivity.
      * eapply cons_argument_values with(v:=Vint Int.one).
        -- apply old_expression_value;constructor.
        -- reflexivity.
        -- eapply cons_argument_values with(v:=Vint Int.zero);
             [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_eof_ready_receive_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory stream initial extra:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_extra=Some(extra,tuchar)->
  environment!_recv=None->gateway_function_binding ge _recv gateway_receive_definition->stream_member_layout ge _descriptor 0->
  (forall before world,property before world->gateway_stream_memory before stream Ptrofs.zero initial)->
  gateway_source_path backend ge gateway_receive_definition(exchange_eof_receive_arguments(stream_descriptor initial)extra)
    (exchange_eof_receive_cont environment(exchange_eof_receive_temps(stream_descriptor initial)temporaries))property
    (Returnstate(Vint Int.zero)(exchange_eof_ready_cont environment temporaries)memory)property.
Proof.
  intros STREAM EXTRA LOCAL FUNCTION LAYOUT CELLS.
  set(ready:=exchange_eof_ready_temps temporaries).
  set(loaded:=exchange_eof_receive_temps(stream_descriptor initial)temporaries).
  eapply gateway_source_same with(target:=State f_host_exchange Sskip exchange_eof_ready_after environment ready memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_ready_test
    (Kseq exchange_eof_after_ready exchange_eof_iteration_cont)environment ready memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip
    (Kseq exchange_eof_after_ready exchange_eof_iteration_cont)environment ready memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_after_ready exchange_eof_iteration_cont environment ready memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_receive_sequence
    (Kseq exchange_eof_after_receive exchange_eof_iteration_cont)environment ready memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_receive_prefix exchange_eof_receive_after environment ready memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_receive_load
    (Kseq exchange_eof_receive_call exchange_eof_receive_after)environment ready memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip
    (Kseq exchange_eof_receive_call exchange_eof_receive_after)environment loaded memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world GOOD;apply certified_set_edge;eapply actual_local_stream_descriptor;
      [exact STREAM|exact LAYOUT|exact(CELLS before world GOOD)].
  - eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_receive_call exchange_eof_receive_after environment loaded memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_source_same with(target:=Callstate gateway_receive_definition(exchange_eof_receive_arguments(stream_descriptor initial)extra)
      (exchange_eof_receive_cont environment loaded)memory);
      [exact CLOSED|cbn;tauto|intros;apply actual_eof_receive_call;[exact EXTRA|exact LOCAL|exact FUNCTION|apply PTree.gss]|
        apply gateway_source_reached;intros;assumption].
Qed.
