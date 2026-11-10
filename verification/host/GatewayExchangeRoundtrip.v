(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One actual exchange sends the request and reads its own reply header. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayStreamRelations
  GatewayHeaderInitialization GatewayHeaderComplete GatewayHeaderFieldMemory GatewayHeaderRuntime GatewayHeaderPacket GatewayHeaderTransfer GatewayHeaderInputs
  GatewayPayloadMemory GatewayRequestSend GatewaySendRuntime GatewaySendState GatewayTransportFrame GatewayReadContext GatewayStackAllocation
  GatewayExchangeTransport GatewayExchangeRequestReceipt GatewayExchangeRuntime GatewayShutdownSource GatewayShutdownSuccess
  GatewayResponseReturn GatewayResponseTransfer GatewayResponseHeader GatewayResponseInputs GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_exchange_initialized_response_header {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (exchange:gateway_exchange_runtime backend io native stable discipline)
    readonly stream header response initial allocation_before allocated environment temporaries object offset header_rows payload_rows command fault
    before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_header=Some(header,tarray tuchar 112)->environment!_stream=Some(stream,Tstruct _host_stream noattr)->
  environment!_response=Some(response,tarray tuchar 24)->
  temporaries!_fields=Some(Vptr object offset)->temporaries!_command=Some(Vint command)->temporaries!_fault=Some(Vint fault)->
  Ptrofs.unsigned offset+320<=Ptrofs.modulus->gateway_header_field_cells before object offset header_rows->
  gateway_payload_field_cells before object offset payload_rows->gateway_payload_rows_readable readonly before payload_rows->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)->
  (forall position,~readonly header position)->(forall position,~readonly stream position)->stream<>header->
  gateway_header_resources native stable discipline None header[stream](GatewayHeaderInputs.gateway_header_readonly readonly stream)
    before world before world->
  Mem.range_perm before header 0 112 Cur Writable->Mem.range_perm before stream 0 48 Cur Writable->
  gateway_stream_memory before stream Ptrofs.zero initial->stream_descriptor initial<>stream_control initial->
  native world response->Mem.range_perm before response 0 24 Cur Writable->
  (forall position,0<=position<24->readonly response position)->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists request_prefix response_prefix body suffix request_memory request_world request_temps response_temps called called_world memory current bytes,
    events=request_prefix++response_prefix++body++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)request_prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment request_temps request_memory)request_world) /\
    gateway_sent_bytes io(stream_descriptor initial)request_prefix=gateway_request_bytes command fault header_rows payload_rows /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment request_temps request_memory)request_world)response_prefix
      (gateway_live(Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)
        (response_transfer_cont environment response_temps)called)called_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)Kstop called)called_world)body
      (gateway_live(Returnstate(Vint Int.zero)Kstop memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(response_transfer_cont environment response_temps)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    Z.of_nat(length bytes)=24 /\gateway_received_bytes io(stream_descriptor initial)(response_prefix++body)=bytes /\
    Mem.loadbytes memory response 0 24=Some(inj_bytes bytes) /\
    exists final,gateway_read_context native stable discipline None stream Ptrofs.zero final response Ptrofs.zero 24
      (gateway_response_readonly(gateway_request_readonly readonly header)response)memory current /\
      gateway_stream_transport_after initial final.
Proof.
  intros ALLOC HEADER STREAM RESPONSE FIELDS COMMAND FAULT SPAN HEADER_CELLS PAYLOAD_CELLS PAYLOADS FIELD_COVER
    HEADER_RO STREAM_RO DIFFERENT RESOURCES HEADER_RANGE STREAM_RANGE STREAM_CELLS SEPARATE RESPONSE_PRIVATE RESPONSE_RANGE RESPONSE_COVER NONNULL RUN.
  destruct(actual_exchange_initialized_request_retained backend io native stable discipline thread_errno runtime readonly stream header initial
    allocation_before allocated environment temporaries object offset header_rows payload_rows command fault before world events value after next
    ALLOC HEADER STREAM FIELDS COMMAND FAULT SPAN HEADER_CELLS PAYLOAD_CELLS PAYLOADS FIELD_COVER HEADER_RO STREAM_RO DIFFERENT RESOURCES
    HEADER_RANGE STREAM_RANGE STREAM_CELLS SEPARATE NONNULL RUN)
    as(source_prefix&sent_prefix&remaining&prepared&prepared_world&request_memory&request_world&called_temps&request_temps&
      E1&QUIET&TO_REQUEST&REQUEST&SENT&SENDING&FAILED&REST&PACKET).
  destruct(gateway_packet_response_allocation native stable discipline None header[stream]
    (GatewayHeaderInputs.gateway_header_readonly readonly stream)before world(gateway_complete_header command fault header_rows)
    prepared prepared_world response PACKET RESPONSE_PRIVATE RESPONSE_RANGE ltac:(intros;left;apply RESPONSE_COVER;assumption))
    as[PREPARED_PRIVATE PREPARED_RANGE].
  assert(STREAM_RESPONSE:stream<>response).
  { pose proof(gateway_alloc_variables_stack(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated
      ALLOC(gateway_empty_stack_environment allocation_before))as[LIVE DISTINCT].
    eapply DISTINCT;[exact STREAM|exact RESPONSE|discriminate]. }
  destruct(gateway_sending_response_context native stable discipline stream response(gateway_request_readonly readonly header)
    prepared prepared_world initial request_memory request_world STREAM_RESPONSE PREPARED_PRIVATE PREPARED_RANGE
    ltac:(intros;left;apply RESPONSE_COVER;assumption)SENDING)as(read_initial&READ_READY&READ_TRANSPORT).
  destruct(actual_exchange_shutdown backend io native stable discipline thread_errno runtime exchange allocation_before allocated environment
    request_temps stream response read_initial(gateway_response_readonly(gateway_request_readonly readonly header)response)
    request_memory request_world remaining value after next ALLOC STREAM FAILED READ_READY NONNULL REST)
    as(shutdown_prefix&after_shutdown&response_memory&response_world&E2&SHUTDOWN&NO_READ&NO_WRITE&RESPONSE_READY&READ_REST).
  set(response_temps:=shutdown_zero_temps(shutdown_temps(stream_descriptor read_initial)request_temps)).
  assert(READ_FAILED:response_temps!_failed=Some(Vint Int.zero)).
  { unfold response_temps,shutdown_zero_temps,shutdown_temps;rewrite !PTree.gso by discriminate;exact FAILED. }
  destruct(actual_exchange_response_header backend io native stable discipline thread_errno runtime allocation_before allocated environment
    response_temps stream response read_initial(gateway_response_readonly(gateway_request_readonly readonly header)response)
    response_memory response_world after_shutdown value after next ALLOC STREAM RESPONSE READ_FAILED RESPONSE_READY NONNULL READ_REST)
    as(select_prefix&body&suffix&called&called_world&memory&current&bytes&E3&SELECT_QUIET&SELECT&RECEIVE&SUFFIX&LENGTH&OBSERVED&LOADED&FINAL&FRAME).
  exists(source_prefix++sent_prefix),(shutdown_prefix++select_prefix),body,suffix,request_memory,request_world,request_temps,
    response_temps,called,called_world,memory,current,bytes.
  split;[rewrite E1,E2,E3;repeat rewrite<-app_assoc;reflexivity|].
  split;[eapply gateway_steps_append;[exact TO_REQUEST|exact REQUEST]|]. split;[exact SENT|].
  split;[eapply gateway_steps_append;[exact SHUTDOWN|exact SELECT]|]. split;[exact RECEIVE|]. split;[exact SUFFIX|].
  split;[exact LENGTH|]. split.
  - rewrite<-(gateway_transport_descriptor initial read_initial READ_TRANSPORT).
    rewrite <-app_assoc,gateway_received_bytes_append,NO_READ;exact OBSERVED.
  - split;[exact LOADED|]. destruct FINAL as[final[READY TRANSPORT]];exists final;split;[exact READY|].
    eapply gateway_transport_transitive;[exact READ_TRANSPORT|exact TRANSPORT].
Qed.
