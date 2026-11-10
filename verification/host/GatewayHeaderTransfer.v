(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The first transfer receives the same complete owned header. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayPrefix GatewayHeaderFields GatewayHeaderPacket GatewayHeaderComplete GatewayReadonly GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition header_transfer_sequence:=match header_fields_after with Ssequence first _=>first|_=>Sskip end.
Definition header_transfer_after:=match header_fields_after with Ssequence _ rest=>rest|_=>Sskip end.
Definition header_transfer_call:=match header_transfer_sequence with Ssequence first _=>first|_=>Sskip end.
Definition header_transfer_bind:=match header_transfer_sequence with Ssequence _ second=>second|_=>Sskip end.
Definition header_transfer_cont environment temporaries:=Kcall(Some _t'30)f_host_exchange environment temporaries
  (Kseq header_transfer_bind(Kseq header_transfer_after Kstop)).
Definition header_transfer_arguments stream header:=[Vptr stream Ptrofs.zero;Vptr header Ptrofs.zero;Vlong(Int64.repr 112);Vint Int.one].

Lemma actual_header_transfer_call ge environment temporaries memory stream header:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_header=Some(header,tarray tuchar 112)->
  environment!_host_transfer=None->gateway_function_binding ge _host_transfer(Internal f_host_transfer)->
  store_edge ge(State f_host_exchange header_transfer_call(Kseq header_transfer_bind(Kseq header_transfer_after Kstop))
    environment temporaries memory)
    (Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)(header_transfer_cont environment temporaries)memory).
Proof.
  intros STREAM HEADER LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr stream Ptrofs.zero).
    + apply local_address_expression;exact STREAM.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vptr header Ptrofs.zero).
      * eapply location_read_value;[apply local_location_value;exact HEADER|apply deref_loc_reference;reflexivity].
      * reflexivity.
      * eapply cons_argument_values with(v:=Vlong(Int64.repr 112)).
        -- split;[constructor;reflexivity|]. intros other VALUE;inversion VALUE;subst;try reflexivity.
           match goal with BAD:eval_lvalue _ _ _ _ (Esizeof _ _)_ _ _|-_=>inversion BAD end.
        -- reflexivity.
        -- eapply cons_argument_values with(v:=Vint Int.one);
             [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_header_transfer_prefix {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory stream header:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_header=Some(header,tarray tuchar 112)->
  environment!_host_transfer=None->gateway_function_binding ge _host_transfer(Internal f_host_transfer)->
  gateway_memory_prefix backend ge
    (Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)(header_transfer_cont environment temporaries)memory)
    property property(State f_host_exchange header_fields_after Kstop environment temporaries memory).
Proof.
  intros STREAM HEADER LOCAL FUNCTION.
  eapply gateway_memory_same with(following:=State f_host_exchange header_transfer_sequence(Kseq header_transfer_after Kstop)
    environment temporaries memory);[exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange header_transfer_call
    (Kseq header_transfer_bind(Kseq header_transfer_after Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)
    (header_transfer_cont environment temporaries)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply actual_header_transfer_call;eassumption.
  - apply gateway_memory_identity.
Qed.
