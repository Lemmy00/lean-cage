(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual stream initializer preserves request/reply read accounting. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers Floats AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadonly GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayPostSpawnContext GatewayPostSpawnCleanup GatewayPostSpawnSource
  GatewayCallerBuffers GatewayCallerFamily GatewayStreamSetupSource GatewayStreamSetupPaths GatewayStreamSetup
  GatewayHeaderInputs GatewayHeaderFieldMemory GatewayPayloadMemory GatewayHeaderRuntime GatewayExchangeRequest
  GatewayReadContext GatewayHeaderTransfer GatewayHeaderInitialization GatewayRequestSend GatewaySendRuntime GatewaySendState GatewayExchangeTransport GatewayExchangeRuntime GatewayExchangeRoundtrip GatewayExchangeReadAccounting GatewayPrimitiveCalls GatewayTransferMath GatewayResponseInputs GatewayResponseReturn GatewayResponseTransfer.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_exchange_stream_response_accounting {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources ipc
    builders genuine footprint(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint)
    (exchange:gateway_exchange_runtime backend io native stable discipline)
    readonly selected reference owner data control stream header response data_left data_right control_left control_right leases
    allocation_before allocated environment temporaries cli cancellation began object offset header_rows payload_rows command fault
    before world events value after next:
  selected data->selected control->selected stream->selected header->selected response->stream<>data->stream<>control->stream<>header->
  (forall position,~readonly stream position)->(forall position,~readonly header position)->
  Mem.range_perm reference stream 0 48 Cur Freeable->Mem.range_perm reference header 0 112 Cur Freeable->Mem.range_perm reference response 0 24 Cur Freeable->
  (forall position,0<=position<24->readonly response position)->
  (forall other position,readonly other position->Mem.perm reference other position Cur Readable)->
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_pair=Some(data,tarray tint 2)->environment!_control=Some(control,tarray tint 2)->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_header=Some(header,tarray tuchar 112)->environment!_response=Some(response,tarray tuchar 24)->
  temporaries!_cli=Some(Vint cli)->temporaries!_cancellation=Some cancellation->temporaries!_began=Some(Vfloat began)->
  ((exists held offset,cancellation=Vptr held offset)\/(exists word,cancellation=Vlong word))->
  temporaries!_fields=Some(Vptr object offset)->temporaries!_command=Some(Vint command)->temporaries!_fault=Some(Vint fault)->
  Ptrofs.unsigned offset+320<=Ptrofs.modulus->gateway_header_field_cells reference object offset header_rows->
  gateway_payload_field_cells reference object offset payload_rows->gateway_payload_rows_readable readonly reference payload_rows->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)->
  Int.repr data_left<>Int.repr control_left->
  gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner data control
    data_left data_right control_left control_right postspawn_empty_builders leases before world->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(postspawn_after 5)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists request_prefix response_prefix body suffix request_memory request_world request_temps response_temps called called_world memory current bytes,
    events=request_prefix++response_prefix++body++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(postspawn_after 5)Kstop environment temporaries before)world)request_prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment request_temps request_memory)request_world) /\
    gateway_sent_bytes io(Int.repr data_left)request_prefix=gateway_request_bytes command fault header_rows payload_rows /\
    gateway_received_bytes io(Int.repr data_left)request_prefix=[] /\
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
    Z.of_nat(length bytes)=24 /\gateway_received_bytes io(Int.repr data_left)(response_prefix++body)=bytes /\
    Mem.loadbytes memory response 0 24=Some(Memdata.inj_bytes bytes) /\
    exists final,gateway_read_context native stable discipline None stream Ptrofs.zero final response Ptrofs.zero 24
      (gateway_response_readonly(gateway_request_readonly readonly header)response)memory current /\
      gateway_stream_transport_after(gateway_initial_stream data_left control_left cli cancellation began)final.

Proof.
  intros DATA_SELECTED CONTROL_SELECTED STREAM_SELECTED HEADER_SELECTED RESPONSE_SELECTED STREAM_DATA STREAM_CONTROL STREAM_HEADER STREAM_RO HEADER_RO
    STREAM_RANGE HEADER_RANGE RESPONSE_RANGE RESPONSE_COVER READABLE ALLOC DATA CONTROL STREAM HEADER RESPONSE CLI CANCELLATION BEGAN POINTER FIELDS COMMAND FAULT SPAN
    HEADER_CELLS PAYLOAD_CELLS PAYLOADS FIELD_COVER SEPARATE READY NONNULL RUN.
  destruct(actual_stream_setup backend io native stable discipline thread_errno resources ipc builders genuine footprint runtime descriptors sdk
    readonly selected reference owner data control stream data_left data_right control_left control_right leases environment temporaries cli cancellation began
    DATA_SELECTED CONTROL_SELECTED STREAM_SELECTED STREAM_DATA STREAM_CONTROL STREAM_RO STREAM_RANGE DATA CONTROL STREAM CLI CANCELLATION BEGAN POINTER
    before world events(Returnstate value Kstop after)next I READY RUN)
    as(p1 & r1 & m1 & w1 & E1 & Q1 & P1 & R1 & CELLS & S1).
  set(header_temps:=stream_setup_temps data_left control_left 8 temporaries).
  pose proof R1 as COPY;destruct COPY as[SIDE VALID GENUINE BUILDERS FAMILY DATA_CELLS CONTROL_CELLS LEASES].
  destruct(FAMILY header HEADER_SELECTED)as[HEADER_LIVE[HEADER_PRIVATE[CURRENT_RO[[FRAME HEADER_PERMISSIONS]HISTORY]]]].
  assert(CURRENT_HEADER:gateway_header_field_cells m1 object offset header_rows).
  { eapply gateway_header_field_cells_retained;[exact HEADER_CELLS|exact FRAME|exact FIELD_COVER]. }
  assert(CURRENT_PAYLOAD:gateway_payload_field_cells m1 object offset payload_rows).
  { eapply gateway_payload_field_cells_retained;[exact PAYLOAD_CELLS|exact FRAME|exact FIELD_COVER]. }
  assert(CURRENT_ROWS:gateway_payload_rows_readable readonly m1 payload_rows).
  { intros index BOUND;destruct(PAYLOADS index BOUND)as[ADDRESS[COVER CONTENT]];split;[exact ADDRESS|].
    split;[exact COVER|]. eapply gateway_payload_bytes_retained;[exact COVER|exact CONTENT|exact FRAME]. }
  assert(RESOURCES:gateway_header_resources native stable discipline None header[stream](GatewayHeaderInputs.gateway_header_readonly readonly stream)m1 w1 m1 w1).
  { eapply gateway_header_inputs_from_parent;[exact R1|exact STREAM_SELECTED|exact HEADER_SELECTED|exact STREAM_RANGE|exact READABLE]. }
  assert(HEADER_WRITABLE:Mem.range_perm m1 header 0 112 Cur Writable).
  { intros position RANGE;eapply Mem.perm_implies.
    - apply(proj1(HEADER_PERMISSIONS header(or_introl eq_refl)position Cur Freeable));apply HEADER_RANGE;exact RANGE.
    - constructor. }
  assert(STREAM_WRITABLE:Mem.range_perm m1 stream 0 48 Cur Writable).
  { destruct(FAMILY stream STREAM_SELECTED)as[LIVE[PRIVATE[RO[[CONTENTS PERMISSIONS]REST]]]].
    intros position RANGE;eapply Mem.perm_implies.
    - apply(proj1(PERMISSIONS stream(or_introl eq_refl)position Cur Freeable));apply STREAM_RANGE;exact RANGE.
    - constructor. }
  destruct(FAMILY response RESPONSE_SELECTED)as[RESPONSE_LIVE[RESPONSE_PRIVATE[RESPONSE_RO[[RESPONSE_FRAME RESPONSE_PERMISSIONS]RESPONSE_HISTORY]]]].
  assert(RESPONSE_WRITABLE:Mem.range_perm m1 response 0 24 Cur Writable).
  { intros position RANGE;eapply Mem.perm_implies.
    - apply(proj1(RESPONSE_PERMISSIONS response(or_introl eq_refl)position Cur Freeable));apply RESPONSE_RANGE;exact RANGE.
    - constructor. }
  destruct(actual_exchange_initialized_response_accounting backend io native stable discipline thread_errno runtime exchange readonly stream header response
    (gateway_initial_stream data_left control_left cli cancellation began)allocation_before allocated environment header_temps object offset header_rows
    payload_rows command fault m1 w1 r1 value after next ALLOC HEADER STREAM RESPONSE
    ltac:(unfold header_temps;rewrite stream_setup_temps_keeps by discriminate;exact FIELDS)
    ltac:(unfold header_temps;rewrite stream_setup_temps_keeps by discriminate;exact COMMAND)
    ltac:(unfold header_temps;rewrite stream_setup_temps_keeps by discriminate;exact FAULT)
    SPAN CURRENT_HEADER CURRENT_PAYLOAD CURRENT_ROWS FIELD_COVER HEADER_RO STREAM_RO STREAM_HEADER RESOURCES
    HEADER_WRITABLE STREAM_WRITABLE CELLS SEPARATE RESPONSE_PRIVATE RESPONSE_WRITABLE RESPONSE_COVER NONNULL S1)
    as(request_prefix&response_prefix&body&suffix&request_memory&request_world&request_temps&response_temps&called&called_world&memory&current&bytes&
      E2&REQUEST&SENT&REQUEST_NO_READ&SELECT&RECEIVE&SUFFIX&LENGTH&OBSERVED&LOADED&FINAL).
  exists(p1++request_prefix),response_prefix,body,suffix,request_memory,request_world,request_temps,response_temps,called,called_world,memory,current,bytes.
  split;[rewrite E1,E2;repeat rewrite<-app_assoc;reflexivity|].
  split;[eapply gateway_steps_append;[exact P1|exact REQUEST]|]. split.
  - rewrite gateway_sent_bytes_append,(gateway_quiet_sent_empty io(Int.repr data_left)p1 Q1);exact SENT.
  - split.
    + rewrite gateway_received_bytes_append,(gateway_quiet_received_empty io(Int.repr data_left)p1 Q1);exact REQUEST_NO_READ.
    + split;[exact SELECT|]. split;[exact RECEIVE|]. split;[exact SUFFIX|].
    split;[exact LENGTH|]. split;[exact OBSERVED|]. split;[exact LOADED|exact FINAL].
Qed.
