(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The same returned result enters the actual EOF readiness loop. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySourcePaths GatewayFramedRuntime
  GatewayPrefix GatewayExchangeTransport.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_eof_loop:=match exchange_eof_phase with Sifthenelse _ first _=>first|_=>Sskip end.
Definition exchange_eof_loop_first:=match exchange_eof_loop with Sloop first _=>first|_=>Sskip end.
Definition exchange_eof_iteration:=match exchange_eof_loop_first with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_eof_ready_sequence:=match exchange_eof_iteration with Ssequence first _=>first|_=>Sskip end.
Definition exchange_eof_after_ready:=match exchange_eof_iteration with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_eof_ready_call:=match exchange_eof_ready_sequence with Ssequence first _=>first|_=>Sskip end.
Definition exchange_eof_ready_test:=match exchange_eof_ready_sequence with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_eof_cont:=Kseq exchange_cleanup_phase Kstop.
Definition exchange_eof_iteration_cont:=Kloop1 exchange_eof_loop_first Sskip exchange_eof_cont.
Definition exchange_eof_ready_after:=Kseq exchange_eof_ready_test(Kseq exchange_eof_after_ready exchange_eof_iteration_cont).
Definition exchange_eof_ready_cont environment temporaries:=Kcall(Some _t'46)f_host_exchange environment temporaries exchange_eof_ready_after.
Definition exchange_eof_ready_arguments stream:=[Vptr stream Ptrofs.zero;Vint Int.one].

Theorem actual_eof_ready_call ge environment temporaries memory stream:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_host_ready=None->
  gateway_function_binding ge _host_ready(Internal f_host_ready)->
  store_edge ge(State f_host_exchange exchange_eof_ready_call exchange_eof_ready_after environment temporaries memory)
    (Callstate(Internal f_host_ready)(exchange_eof_ready_arguments stream)(exchange_eof_ready_cont environment temporaries)memory).
Proof.
  intros STREAM LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr stream Ptrofs.zero).
    + apply local_address_expression;exact STREAM.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint Int.one);
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_eof_iteration_ready_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory stream:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_host_ready=None->
  gateway_function_binding ge _host_ready(Internal f_host_ready)->
  gateway_source_path backend ge(Internal f_host_ready)(exchange_eof_ready_arguments stream)
    (exchange_eof_ready_cont environment temporaries)property
    (State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries memory)property.
Proof.
  intros STREAM LOCAL FUNCTION.
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_loop_first exchange_eof_iteration_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  eapply gateway_source_same with(target:=State f_host_exchange Sskip(Kseq exchange_eof_iteration exchange_eof_iteration_cont)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_iteration exchange_eof_iteration_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_ready_sequence
    (Kseq exchange_eof_after_ready exchange_eof_iteration_cont)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_ready_call exchange_eof_ready_after environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=Callstate(Internal f_host_ready)(exchange_eof_ready_arguments stream)
    (exchange_eof_ready_cont environment temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply actual_eof_ready_call;assumption|apply gateway_source_reached;intros;assumption].
Qed.

Theorem actual_eof_enter_ready_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory stream object offset:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_host_ready=None->
  gateway_function_binding ge _host_ready(Internal f_host_ready)->temporaries!_result=Some(Vptr object offset)->
  (forall before world,property before world->Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)=true)->
  gateway_source_path backend ge(Internal f_host_ready)(exchange_eof_ready_arguments stream)
    (exchange_eof_ready_cont environment temporaries)property
    (State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries memory)property.
Proof.
  intros STREAM LOCAL FUNCTION RESULT POINTER.
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_phase exchange_eof_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto| |apply actual_eof_iteration_ready_path;assumption].
  intros before world READY;apply certified_if_edge with(v:=Vptr object offset)(b:=true).
  - apply old_expression_value,value_temp;exact RESULT.
  - change((if Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)then Some true else None)=Some true).
    rewrite(POINTER before world READY);reflexivity.
Qed.
