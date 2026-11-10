(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Cleanup closes the same two source-loaded private endpoints. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayExchangeTransport GatewayStreamInterface GatewayStreamLayout GatewayShutdownSource GatewaySpawnABI.
Import ListNotations.
Open Scope Z_scope.

Fixpoint exchange_cleanup_after(index:nat):statement:=
  match index with O=>exchange_cleanup_phase|S previous=>
    match exchange_cleanup_after previous with Ssequence _ rest=>rest|_=>Sskip end end.
Definition exchange_cleanup_statement index:=match exchange_cleanup_after index with Ssequence first _=>first|_=>Sskip end.
Inductive gateway_cleanup_endpoint:=gateway_cleanup_data|gateway_cleanup_control.
Definition cleanup_close_index endpoint:=match endpoint with gateway_cleanup_data=>0%nat|gateway_cleanup_control=>1%nat end.
Definition cleanup_close_temp endpoint:=match endpoint with gateway_cleanup_data=>_t'57|gateway_cleanup_control=>_t'56 end.
Definition cleanup_close_value endpoint initial:=match endpoint with
  gateway_cleanup_data=>stream_descriptor initial|gateway_cleanup_control=>stream_control initial end.
Definition cleanup_close_body endpoint:=exchange_cleanup_statement(cleanup_close_index endpoint).
Definition cleanup_close_load endpoint:=match cleanup_close_body endpoint with Ssequence first _=>first|_=>Sskip end.
Definition cleanup_close_call endpoint:=match cleanup_close_body endpoint with Ssequence _ rest=>rest|_=>Sskip end.
Definition cleanup_close_after endpoint:=Kseq(exchange_cleanup_after(S(cleanup_close_index endpoint)))Kstop.
Definition cleanup_close_temps endpoint descriptor(temporaries:temp_env):=PTree.set(cleanup_close_temp endpoint)(Vint descriptor)temporaries.
Definition cleanup_close_cont endpoint environment temporaries:=Kcall None f_host_exchange environment temporaries(cleanup_close_after endpoint).

Lemma actual_local_stream_control ge environment temporaries memory stream initial:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->stream_member_layout ge _control 4->
  gateway_stream_memory memory stream Ptrofs.zero initial->
  expression_value ge environment temporaries memory
    (Efield(Evar _stream(Tstruct _host_stream noattr))_control tint)(Vint(stream_control initial)).
Proof.
  intros STREAM[composite[LAYOUT MEMBER]]CELLS.
  eapply location_read_value with(b:=stream)(ofs:=Ptrofs.add Ptrofs.zero(Ptrofs.repr 4)).
  - eapply struct_location_value with(id:=_host_stream)(co:=composite)(att:=noattr)(delta:=4);
      [eapply location_read_value;[apply local_location_value;exact STREAM|apply deref_loc_copy;reflexivity]|
        reflexivity|exact LAYOUT|exact MEMBER].
  - eapply deref_loc_value;[reflexivity|exact(proj1(proj2 CELLS))].
Qed.

Theorem actual_cleanup_close_call ge endpoint environment temporaries memory descriptor:
  temporaries!(cleanup_close_temp endpoint)=Some(Vint descriptor)->environment!_close=None->
  gateway_function_binding ge _close(gateway_spawn_signature gateway_close_api)->
  store_edge ge(State f_host_exchange(cleanup_close_call endpoint)(cleanup_close_after endpoint)environment temporaries memory)
    (Callstate(gateway_spawn_signature gateway_close_api)[Vint descriptor](cleanup_close_cont endpoint environment temporaries)memory).
Proof.
  intros VALUE LOCAL[symbol[SYMBOL FUNCTION]];destruct endpoint;
    eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  all:try reflexivity.
  all:try solve[apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity]].
  all:try solve[eapply cons_argument_values with(v:=Vint descriptor);
    [apply old_expression_value,value_temp;exact VALUE|reflexivity|apply no_argument_values]].
  all:cbn;exact FUNCTION.
Qed.

Theorem actual_cleanup_close_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)endpoint environment temporaries memory stream initial:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->stream_member_layout ge _descriptor 0->
  stream_member_layout ge _control 4->environment!_close=None->
  gateway_function_binding ge _close(gateway_spawn_signature gateway_close_api)->
  (forall before world,property before world->gateway_stream_memory before stream Ptrofs.zero initial)->
  gateway_memory_prefix backend ge
    (Callstate(gateway_spawn_signature gateway_close_api)[Vint(cleanup_close_value endpoint initial)]
      (cleanup_close_cont endpoint environment(cleanup_close_temps endpoint(cleanup_close_value endpoint initial)temporaries))memory)
    property property
    (State f_host_exchange(exchange_cleanup_after(cleanup_close_index endpoint))Kstop environment temporaries memory).
Proof.
  intros STREAM DESCRIPTOR CONTROL LOCAL FUNCTION CELLS.
  eapply gateway_memory_same with(following:=State f_host_exchange(cleanup_close_body endpoint)
    (cleanup_close_after endpoint)environment temporaries memory);
    [exact CLOSED|destruct endpoint;cbn;tauto|intros;destruct endpoint;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange(cleanup_close_load endpoint)
    (Kseq(cleanup_close_call endpoint)(cleanup_close_after endpoint))environment temporaries memory);
    [exact CLOSED|destruct endpoint;cbn;tauto|intros;destruct endpoint;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq(cleanup_close_call endpoint)(cleanup_close_after endpoint))environment
    (cleanup_close_temps endpoint(cleanup_close_value endpoint initial)temporaries)memory);
    [exact CLOSED|destruct endpoint;cbn;tauto| |].
  - intros before world READY;destruct endpoint;apply certified_set_edge.
    + eapply actual_local_stream_descriptor;[exact STREAM|exact DESCRIPTOR|exact(CELLS before world READY)].
    + eapply actual_local_stream_control;[exact STREAM|exact CONTROL|exact(CELLS before world READY)].
  - eapply gateway_memory_same with(following:=State f_host_exchange(cleanup_close_call endpoint)
      (cleanup_close_after endpoint)environment(cleanup_close_temps endpoint(cleanup_close_value endpoint initial)temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=Callstate(gateway_spawn_signature gateway_close_api)[Vint(cleanup_close_value endpoint initial)]
      (cleanup_close_cont endpoint environment(cleanup_close_temps endpoint(cleanup_close_value endpoint initial)temporaries))memory);
      [exact CLOSED|destruct endpoint;cbn;tauto|intros;apply actual_cleanup_close_call;
        [apply PTree.gss|exact LOCAL|exact FUNCTION]|apply gateway_memory_identity].
Qed.

Theorem actual_cleanup_close_return_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)endpoint environment temporaries memory:
  gateway_memory_prefix backend ge
    (State f_host_exchange(exchange_cleanup_after(S(cleanup_close_index endpoint)))Kstop environment temporaries memory)property property
    (State f_host_exchange Sskip(cleanup_close_after endpoint)environment temporaries memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange(exchange_cleanup_after(S(cleanup_close_index endpoint)))Kstop
    environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
