(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original reply call receives its exact twenty-four header bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayReadonly
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayThreadRuntime GatewayRuntimeABI GatewayStreamInterface
  GatewayReadContext GatewayPrefix GatewayReadyActual GatewayTransferBuffer GatewayTransferPost GatewayTransferState GatewayTransportFrame
  GatewayReturnTypes GatewayExchangeTransport GatewayResponseReturn GatewayStreamLayout.
Import ListNotations.
Open Scope Z_scope.

Definition response_transfer_arguments stream response:=
  [Vptr stream Ptrofs.zero;Vptr response Ptrofs.zero;Vlong(Int64.repr 24);Vint Int.zero].

Lemma actual_response_transfer_call ge environment temporaries memory stream response:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_response=Some(response,tarray tuchar 24)->
  environment!_host_transfer=None->gateway_function_binding ge _host_transfer(Internal f_host_transfer)->
  store_edge ge(State f_host_exchange response_transfer_call
    (Kseq response_transfer_bind(Kseq(exchange_transport_after 3)Kstop))environment temporaries memory)
    (Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)(response_transfer_cont environment temporaries)memory).
Proof.
  intros STREAM RESPONSE LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr stream Ptrofs.zero).
    + apply local_address_expression;exact STREAM.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vptr response Ptrofs.zero).
      * eapply location_read_value;[apply local_location_value;exact RESPONSE|apply deref_loc_reference;reflexivity].
      * reflexivity.
      * eapply cons_argument_values with(v:=Vlong(Int64.repr 24)).
        -- split;[constructor;reflexivity|]. intros other VALUE;inversion VALUE;subst;try reflexivity.
           match goal with BAD:eval_lvalue _ _ _ _ (Esizeof _ _)_ _ _|-_=>inversion BAD end.
        -- reflexivity.
        -- eapply cons_argument_values with(v:=Vint Int.zero);
             [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_response_transfer_prefix {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory stream response:
  temporaries!_failed=Some(Vint Int.zero)->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_response=Some(response,tarray tuchar 24)->
  environment!_host_transfer=None->gateway_function_binding ge _host_transfer(Internal f_host_transfer)->
  gateway_memory_prefix backend ge
    (Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)(response_transfer_cont environment temporaries)memory)
    property property(State f_host_exchange(exchange_transport_after 2)Kstop environment temporaries memory).
Proof.
  intros FAILED STREAM RESPONSE LOCAL FUNCTION.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_response_phase
    (Kseq(exchange_transport_after 3)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange response_transfer_body
    (Kseq(exchange_transport_after 3)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  { intros before world READY;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value;WriteAll.expression|reflexivity]. }
  eapply gateway_memory_same with(following:=State f_host_exchange response_transfer_call
    (Kseq response_transfer_bind(Kseq(exchange_transport_after 3)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)
    (response_transfer_cont environment temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;eapply actual_response_transfer_call;eassumption|apply gateway_memory_identity].
Qed.

Theorem gateway_actual_response_buffer {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    stream response initial readonly before world events after next:
  gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists bytes, Z.of_nat(length bytes)=24 /\gateway_received_bytes io(stream_descriptor initial)events=bytes /\
    Mem.loadbytes after response 0 24=Some(inj_bytes bytes) /\
    gateway_transfer_state native stable discipline stream Ptrofs.zero response readonly initial after next /\
    gateway_transport_frame native readonly stream Ptrofs.zero response Ptrofs.zero 24 before world after next.
Proof.
  intros READY RUN.
  pose proof(proj1(Forall_forall _ _)actual_gateway_transfer_functions)as TABLE.
  destruct(TABLE(_host_ready,Internal f_host_ready)ltac:(cbn;tauto))as(ready_symbol&READY_SYMBOL&READY_FUNCTION).
  destruct(TABLE(_PyEval_SaveThread,gateway_save_thread_definition)ltac:(cbn;tauto))as(save_symbol&SAVE_SYMBOL&SAVE_FUNCTION).
  destruct(TABLE(_recv,gateway_receive_definition)ltac:(cbn;tauto))as(receive_symbol&RECEIVE_SYMBOL&RECEIVE_FUNCTION).
  destruct(TABLE(___errno_location,gateway_errno_location_definition)ltac:(cbn;tauto))as(errno_symbol&ERRNO_SYMBOL&ERRNO_FUNCTION).
  destruct(TABLE(_PyEval_RestoreThread,gateway_restore_thread_definition)ltac:(cbn;tauto))as(restore_symbol&RESTORE_SYMBOL&RESTORE_FUNCTION).
  destruct actual_stream_layout as[DESCRIPTOR REST].
  exact(actual_receive_transfer_buffer backend io native stable discipline thread_errno runtime(Clight.globalenv prog)
    (gateway_actual_ready_producer backend io native stable discipline thread_errno runtime)
    stream response Ptrofs.zero readonly Ptrofs.zero ready_symbol save_symbol receive_symbol errno_symbol restore_symbol
    READY_SYMBOL READY_FUNCTION SAVE_SYMBOL SAVE_FUNCTION RECEIVE_SYMBOL RECEIVE_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION
    RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR events initial 24 before world after next READY RUN).
Qed.

Theorem actual_successful_response_receives {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    environment temporaries stream response initial readonly before world events value after next:
  gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly before world->
  value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)
      (response_transfer_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current bytes,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)Kstop before)world)prefix
      (gateway_live(Returnstate(Vint Int.zero)Kstop memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(response_transfer_cont environment temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    Z.of_nat(length bytes)=24 /\gateway_received_bytes io(stream_descriptor initial)prefix=bytes /\
    Mem.loadbytes memory response 0 24=Some(inj_bytes bytes) /\
    (exists final, gateway_read_context native stable discipline None stream Ptrofs.zero final response Ptrofs.zero 24 readonly memory current /\
      gateway_stream_transport_after initial final) /\
    gateway_transport_frame native readonly stream Ptrofs.zero response Ptrofs.zero 24 before world memory current.
Proof.
  intros READY NONNULL RUN.
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_transfer)(response_transfer_arguments stream response)
    (response_transfer_cont environment temporaries)before world events(Returnstate value Kstop after)next I ltac:(cbn;lia)RUN)
    as(prefix&suffix&returned&memory&current&EVENTS&BODY&SUFFIX).
  pose proof(gateway_actual_int_return backend(Clight.globalenv prog)f_host_transfer(response_transfer_arguments stream response)
    before world prefix returned memory current actual_host_transfer_return_profile BODY)as TYPE.
  pose proof(actual_successful_response_return backend(Clight.globalenv prog)environment temporaries memory current suffix returned
    value after next TYPE NONNULL SUFFIX)as ZERO;subst returned.
  destruct(gateway_actual_response_buffer backend io native stable discipline thread_errno runtime stream response initial readonly
    before world prefix memory current READY BODY)as(bytes&LENGTH&OBSERVED&LOADED&STATE&FRAME).
  exists prefix,suffix,memory,current,bytes.
  split;[exact EVENTS|]. split;[exact BODY|]. split;[exact SUFFIX|].
  split;[exact LENGTH|]. split;[exact OBSERVED|]. split;[exact LOADED|]. split;[|exact FRAME].
  eapply gateway_transfer_read_context;[exact(proj2(proj2(proj2(proj2 READY))))|exact STATE|exact FRAME].
Qed.
