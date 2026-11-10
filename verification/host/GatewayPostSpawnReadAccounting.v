(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same post-spawn source preserves the request/reply byte boundary. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers Floats AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadonly GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayPostSpawnContext GatewayPostSpawnCleanup GatewayPostSpawnSource
  GatewayCallerBuffers GatewayCallerFamily GatewayPostSpawnGuard GatewayPostSpawnClose GatewayFramedRuntime GatewayMemoryPrefixes GatewayStreamRequest GatewayStreamSetupSource GatewayStreamSetupPaths GatewayStreamSetup
  GatewayHeaderInputs GatewayHeaderFieldMemory GatewayPayloadMemory GatewayHeaderRuntime GatewayExchangeRequest
  GatewayHeaderTransfer GatewayHeaderInitialization GatewayRequestSend GatewaySendRuntime GatewaySendState GatewayExchangeTransport GatewayExchangeRuntime GatewayStreamRoundtrip GatewayStreamReadAccounting GatewayPrimitiveCalls GatewayTransferMath GatewayResponseReturn GatewayResponseTransfer GatewayResponseInputs GatewayReadContext.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_exchange_postspawn_response_accounting {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources ipc
    builders genuine footprint(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint)
    (exchange:gateway_exchange_runtime backend io native stable discipline)
    readonly selected reference owner data control stream header response data_left data_right control_left control_right leases
    actions attributes plan settings data_entry control_entry allocation_before allocated environment temporaries cli cancellation began object offset header_rows payload_rows command fault
    before world events value after next:
  selected data->selected control->selected stream->selected header->selected response->selected actions->selected attributes->
  actions<>data->actions<>control->attributes<>data->attributes<>control->
  (forall position,~readonly actions position)->(forall position,~readonly attributes position)->
  Mem.range_perm reference actions 0 80 Cur Freeable->Mem.range_perm reference attributes 0 336 Cur Freeable->
  stream<>data->stream<>control->stream<>header->
  (forall position,~readonly stream position)->(forall position,~readonly header position)->
  Mem.range_perm reference stream 0 48 Cur Freeable->Mem.range_perm reference header 0 112 Cur Freeable->Mem.range_perm reference response 0 24 Cur Freeable->
  (forall position,0<=position<24->readonly response position)->
  (forall other position,readonly other position->Mem.perm reference other position Cur Readable)->
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_actions=Some(actions,GatewaySpawnABI.gateway_actions_type)->
  environment!_attributes=Some(attributes,GatewaySpawnABI.gateway_attributes_type)->
  environment!_pair=Some(data,tarray tint 2)->environment!_control=Some(control,tarray tint 2)->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_header=Some(header,tarray tuchar 112)->environment!_response=Some(response,tarray tuchar 24)->
  temporaries!_started=Some(Vint Int.zero)->temporaries!_cli=Some(Vint cli)->temporaries!_cancellation=Some cancellation->temporaries!_began=Some(Vfloat began)->
  ((exists held offset,cancellation=Vptr held offset)\/(exists word,cancellation=Vlong word))->
  temporaries!_fields=Some(Vptr object offset)->temporaries!_command=Some(Vint command)->temporaries!_fault=Some(Vint fault)->
  Ptrofs.unsigned offset+320<=Ptrofs.modulus->gateway_header_field_cells reference object offset header_rows->
  gateway_payload_field_cells reference object offset payload_rows->gateway_payload_rows_readable readonly reference payload_rows->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)->
  Int.repr data_left<>Int.repr control_left->
  In(data_right,data_entry)leases->In(control_right,control_entry)leases->data_right<>control_right->
  gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner data control
    data_left data_right control_left control_right(postspawn_initial_builders actions attributes plan settings)leases before world->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(postspawn_after 0)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists request_prefix response_prefix body suffix request_memory request_world request_temps response_temps called called_world memory current bytes,
    events=request_prefix++response_prefix++body++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(postspawn_after 0)Kstop environment temporaries before)world)request_prefix
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
  intros DATA_SELECTED CONTROL_SELECTED STREAM_SELECTED HEADER_SELECTED RESPONSE_SELECTED ACTIONS_SELECTED ATTRIBUTES_SELECTED
    ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA ATTRIBUTES_CONTROL ACTIONS_RO ATTRIBUTES_RO ACTIONS_RANGE ATTRIBUTES_RANGE
    STREAM_DATA STREAM_CONTROL STREAM_HEADER STREAM_RO HEADER_RO STREAM_RANGE HEADER_RANGE RESPONSE_RANGE RESPONSE_COVER READABLE ALLOC ACTIONS ATTRIBUTES DATA CONTROL
    STREAM HEADER RESPONSE STARTED CLI CANCELLATION BEGAN POINTER FIELDS COMMAND FAULT SPAN HEADER_CELLS PAYLOAD_CELLS PAYLOADS FIELD_COVER
    SEPARATE DATA_ENTRY CONTROL_ENTRY PEERS READY NONNULL RUN.
  destruct(actual_postspawn_cleanup backend io native stable discipline thread_errno resources ipc builders genuine footprint
    runtime descriptors sdk readonly selected reference owner data control data_left data_right control_left control_right actions attributes
    DATA_SELECTED CONTROL_SELECTED ACTIONS_SELECTED ATTRIBUTES_SELECTED ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA ATTRIBUTES_CONTROL
    ACTIONS_RO ATTRIBUTES_RO ACTIONS_RANGE ATTRIBUTES_RANGE plan settings leases data_entry control_entry allocation_before allocated environment
    temporaries before world events value after next(Int.repr data_left)ALLOC ACTIONS ATTRIBUTES DATA CONTROL READY DATA_ENTRY CONTROL_ENTRY PEERS RUN)
    as(p1 & r1 & m1 & w1 & E1 & P1 & R1 & INPUT_EMPTY & OUTPUT_EMPTY & S1).
  set(cleaned:=postspawn_cleanup_temps data_right control_right temporaries).
  set(kept:=postspawn_cleanup_leases data_right control_right leases).
  set(context:=gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner data control
    data_left data_right control_left control_right postspawn_empty_builders kept).
  assert(CLOSED:gateway_ambient_closed backend context).
  { eapply gateway_postspawn_ambient;[exact runtime|exact descriptors|exact sdk|exact DATA_SELECTED|exact CONTROL_SELECTED]. }
  assert(ZERO:cleaned!_started=Some(Vint Int.zero)).
  { unfold cleaned;rewrite postspawn_cleanup_keeps by discriminate;exact STARTED. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m1 w1 r1(Returnstate value Kstop after)next
    (actual_postspawn_zero_guard backend(Clight.globalenv prog)context CLOSED environment cleaned m1 ZERO)I R1 S1)
    as(p2 & r2 & m2 & w2 & E2 & Q2 & P2 & R2 & S2).
  cbn[gateway_replace_memory]in P2,S2.
  destruct(actual_exchange_stream_response_accounting backend io native stable discipline thread_errno resources ipc builders genuine footprint runtime descriptors sdk exchange
    readonly selected reference owner data control stream header response data_left data_right control_left control_right kept
    allocation_before allocated environment cleaned cli cancellation began object offset header_rows payload_rows command fault m2 w2 r2 value after next
    DATA_SELECTED CONTROL_SELECTED STREAM_SELECTED HEADER_SELECTED RESPONSE_SELECTED STREAM_DATA STREAM_CONTROL STREAM_HEADER STREAM_RO HEADER_RO
    STREAM_RANGE HEADER_RANGE RESPONSE_RANGE RESPONSE_COVER READABLE ALLOC DATA CONTROL STREAM HEADER RESPONSE
    ltac:(unfold cleaned;rewrite postspawn_cleanup_keeps by discriminate;exact CLI)
    ltac:(unfold cleaned;rewrite postspawn_cleanup_keeps by discriminate;exact CANCELLATION)
    ltac:(unfold cleaned;rewrite postspawn_cleanup_keeps by discriminate;exact BEGAN)POINTER
    ltac:(unfold cleaned;rewrite postspawn_cleanup_keeps by discriminate;exact FIELDS)
    ltac:(unfold cleaned;rewrite postspawn_cleanup_keeps by discriminate;exact COMMAND)
    ltac:(unfold cleaned;rewrite postspawn_cleanup_keeps by discriminate;exact FAULT)
    SPAN HEADER_CELLS PAYLOAD_CELLS PAYLOADS FIELD_COVER SEPARATE R2 NONNULL S2)
    as(request_prefix&response_prefix&body&suffix&request_memory&request_world&request_temps&response_temps&called&called_world&memory&current&bytes&
      E3&REQUEST&SENT&REQUEST_NO_READ&SELECT&RECEIVE&SUFFIX&LENGTH&OBSERVED&LOADED&FINAL).
  exists(p1++p2++request_prefix),response_prefix,body,suffix,request_memory,request_world,request_temps,response_temps,
    called,called_world,memory,current,bytes.
  split;[rewrite E1,E2,E3;repeat rewrite<-app_assoc;reflexivity|].
  split;[eapply gateway_steps_append;[exact P1|eapply gateway_steps_append;[exact P2|exact REQUEST]]|]. split.
  - rewrite !gateway_sent_bytes_append,OUTPUT_EMPTY,(gateway_quiet_sent_empty io(Int.repr data_left)p2 Q2);exact SENT.
  - split.
    + rewrite !gateway_received_bytes_append,INPUT_EMPTY,(gateway_quiet_received_empty io(Int.repr data_left)p2 Q2);exact REQUEST_NO_READ.
    + split;[exact SELECT|]. split;[exact RECEIVE|]. split;[exact SUFFIX|].
    split;[exact LENGTH|]. split;[exact OBSERVED|]. split;[exact LOADED|exact FINAL].
Qed.
