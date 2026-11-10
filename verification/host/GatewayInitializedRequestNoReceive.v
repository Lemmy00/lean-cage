(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual initialized request leaves its response queue untouched. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayThreadRuntime GatewayStreamInterface GatewayStreamRelations
  GatewayReadContext GatewaySendInterface GatewaySendState GatewayTransportFrame GatewaySendRuntime GatewayReadonly
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayFieldStores GatewayFieldGuard GatewayLayout GatewayExchangeSetup GatewayHeaderInitialization
  GatewayHeaderFields GatewayHeaderFieldMemory GatewayHeaderRuntime GatewayHeaderPacket GatewayHeaderComplete GatewayHeaderTransfer
  GatewayHeaderInputs GatewayPayloadMemory GatewayPayloadLoop GatewayRequestSend GatewayRequestNoReceive GatewayPrimitiveCalls GatewayTransferMath GatewayExchangeTransport GatewayExchangeRequest.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_exchange_initialized_request_no_receive {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    readonly stream header initial allocation_before allocated environment temporaries object offset header_rows payload_rows command fault
    before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_header=Some(header,tarray tuchar 112)->environment!_stream=Some(stream,Tstruct _host_stream noattr)->
  temporaries!_fields=Some(Vptr object offset)->temporaries!_command=Some(Vint command)->temporaries!_fault=Some(Vint fault)->
  Ptrofs.unsigned offset+320<=Ptrofs.modulus->gateway_header_field_cells before object offset header_rows->
  gateway_payload_field_cells before object offset payload_rows->gateway_payload_rows_readable readonly before payload_rows->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)->
  (forall position,~readonly header position)->(forall position,~readonly stream position)->stream<>header->
  gateway_header_resources native stable discipline None header[stream](gateway_header_readonly readonly stream)before world before world->
  Mem.range_perm before header 0 112 Cur Writable->Mem.range_perm before stream 0 48 Cur Writable->
  gateway_stream_memory before stream Ptrofs.zero initial->stream_descriptor initial<>stream_control initial->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists source_prefix request_prefix suffix prepared prepared_world memory current called_temps final_temps,
    events=source_prefix++request_prefix++suffix /\Forall gateway_quiet_event source_prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)source_prefix
      (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)
        (header_transfer_cont environment called_temps)prepared)prepared_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)
        (header_transfer_cont environment called_temps)prepared)prepared_world)request_prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment final_temps memory)current) /\
    gateway_sent_bytes io(stream_descriptor initial)(source_prefix++request_prefix)=gateway_request_bytes command fault header_rows payload_rows /\
    gateway_received_bytes io(stream_descriptor initial)(source_prefix++request_prefix)=[] /\
    gateway_sending_state native stable discipline stream(gateway_request_readonly readonly header)prepared prepared_world initial memory current /\
    final_temps!_failed=Some(Vint Int.zero) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_header_packet native stable discipline None header[stream](GatewayHeaderInputs.gateway_header_readonly readonly stream)
      before world(gateway_complete_header command fault header_rows)prepared prepared_world.
Proof.
  intros ALLOC HEADER STREAM FIELDS COMMAND FAULT SPAN HEADER_CELLS PAYLOAD_CELLS PAYLOADS FIELD_COVER HEADER_RO STREAM_RO DISTINCT
    RESOURCES HEADER_WRITABLE STREAM_WRITABLE STREAM_CELLS SEPARATE NONNULL RUN.
  set(held_ro:=gateway_header_readonly readonly stream).
  assert(HEADER_AWAY:forall position,0<=position<112->~held_ro header position).
  { intros position RANGE[OLD|[SAME INSIDE]];[exact(HEADER_RO position OLD)|congruence]. }
  destruct(actual_exchange_header_boundary_bytes backend io native stable discipline thread_errno runtime None header[stream]held_ro
    before world allocation_before allocated environment temporaries object offset header_rows command fault before world events
    (Returnstate value Kstop after)next eq_refl ALLOC HEADER FIELDS COMMAND FAULT SPAN HEADER_CELLS
    ltac:(intros position RANGE;left;apply FIELD_COVER;exact RANGE)HEADER_AWAY RESOURCES HEADER_WRITABLE RUN)
    as(p1 & r1 & m1 & w1 & called_temps & E1 & Q1 & P1 & R1 & BYTES1 & TEMPS & S1).
  set(packet:=gateway_header_packet native stable discipline None header[stream]held_ro before world
    (gateway_complete_header command fault header_rows)).
  assert(CLOSED:gateway_ambient_closed backend packet).
  { apply gateway_header_packet_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. }
  assert(LOCAL:environment!_host_transfer=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(FUNCTION:gateway_function_binding(Clight.globalenv prog)_host_transfer(Internal f_host_transfer)).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m1 w1 r1(Returnstate value Kstop after)next
    (actual_header_transfer_prefix backend(Clight.globalenv prog)packet CLOSED environment called_temps m1 stream header
      STREAM HEADER LOCAL FUNCTION)I R1 S1)
    as(p2 & r2 & prepared & prepared_world & E2 & Q2 & P2 & R2 & S2).
  cbn[gateway_replace_memory]in P2,S2.
  pose proof R2 as PACKET;destruct PACKET as[PREPARED HEADER_READY LENGTH BYTES].
  pose proof PREPARED as PREPARED_COPY;destruct PREPARED_COPY as[SIDE PRIVATE LIVE HELD RO FRAME PERMISSIONS NATIVE STABLE].
  assert(OLD_FRAME:Mem.unchanged_on readonly before prepared).
  { eapply Mem.unchanged_on_implies;[exact FRAME|]. intros other position HERE VALID;left;exact HERE. }
  set(request_ro:=gateway_request_readonly readonly header).
  assert(CURRENT_CELLS:gateway_payload_field_cells prepared object offset payload_rows).
  { eapply gateway_payload_field_cells_retained;[exact PAYLOAD_CELLS|exact OLD_FRAME|exact FIELD_COVER]. }
  assert(CURRENT_PAYLOADS:gateway_payload_rows_readable request_ro prepared payload_rows).
  { intros index BOUND;destruct(PAYLOADS index BOUND)as[ADDRESS[COVER BYTES_OLD]].
    split;[exact ADDRESS|]. split.
    - eapply gateway_payload_cover_included;[intros other position HERE;left;exact HERE|exact COVER].
    - eapply gateway_payload_bytes_retained;[exact COVER|exact BYTES_OLD|exact OLD_FRAME]. }
  destruct(gateway_request_send_inputs backend io native stable discipline thread_errno runtime readonly stream header initial
    before world(gateway_complete_header command fault header_rows)prepared prepared_world R2 STREAM_CELLS STREAM_WRITABLE DISTINCT STREAM_RO)
    as[INPUT[SIDE_AFTER[PRIVATE_AFTER STABLE_AFTER]]].
  assert(SENDING:gateway_sending_state native stable discipline stream request_ro prepared prepared_world initial prepared prepared_world).
  { exists initial;split.
    - split;[exact SIDE_AFTER|]. split;[exact PRIVATE_AFTER|]. split;[exact PRIVATE_AFTER|]. split;assumption.
    - split;[apply gateway_transport_refl|apply gateway_transport_frame_refl]. }
  assert(FIELDS_AFTER:called_temps!_fields=Some(Vptr object offset)).
  { rewrite(TEMPS _fields);try discriminate;exact FIELDS. }
  assert(HEADER_BYTES:Mem.loadbytes prepared header 0 112=Some(inj_bytes(gateway_complete_header command fault header_rows))).
  { rewrite gateway_complete_header_length in BYTES;exact BYTES. }
  destruct(actual_exchange_request_no_receive backend io native stable discipline thread_errno runtime stream header request_ro prepared prepared_world
    initial environment object offset payload_rows STREAM LOCAL FUNCTION actual_header_field_size
    ltac:(exact(proj1(proj2(proj2 actual_field_layout))))ltac:(exact(proj1(proj2 actual_field_layout)))
    SPAN CURRENT_CELLS ltac:(intros position RANGE;left;apply FIELD_COVER;exact RANGE)CURRENT_PAYLOADS SEPARATE
    called_temps command fault header_rows prepared prepared_world r2 value after next FIELDS_AFTER SENDING
    ltac:(intros position RANGE;right;split;[reflexivity|exact RANGE])HEADER_BYTES NONNULL S2)
    as(request_prefix & suffix & memory & current & final_temps & E3 & REQUEST & OBSERVED & NO_RECEIVE & FINAL & FAILED & SUFFIX).
  exists(p1++p2),request_prefix,suffix,prepared,prepared_world,memory,current,called_temps,final_temps.
  split;[rewrite E1,E2,E3;repeat rewrite<-app_assoc;reflexivity|].
  split;[apply Forall_app;split;assumption|].
  split;[eapply gateway_steps_append;[exact P1|exact P2]|]. split;[exact REQUEST|].
  split.
  - rewrite gateway_sent_bytes_append,(gateway_quiet_sent_empty io(stream_descriptor initial)(p1++p2)
      ltac:(apply Forall_app;split;assumption));exact OBSERVED.
  - split.
    + rewrite gateway_received_bytes_append,(gateway_quiet_received_empty io(stream_descriptor initial)(p1++p2)
        ltac:(apply Forall_app;split;assumption));exact NO_RECEIVE.
    + split;[exact FINAL|]. split;[exact FAILED|]. split;[exact SUFFIX|exact R2].
Qed.
