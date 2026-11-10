(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual outgoing bytes equal the same source-constructed header. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Events Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayThreadRuntime
  GatewayHeaderTransfer GatewayHeaderComplete GatewaySendActual GatewaySendInterface GatewaySendRuntime
  GatewayTransportFrame.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_header_send {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    before world stream header initial readonly command fault rows events after next:
  discipline None before world->native world stream->
  (forall object position,readonly object position->stable world object position)->
  gateway_send_inputs before stream Ptrofs.zero initial readonly->
  (forall position,0<=position<112->readonly header position)->
  Mem.loadbytes before header 0 112=Some(inj_bytes(gateway_complete_header command fault rows))->
  stream_descriptor initial<>stream_control initial->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  gateway_sent_bytes io(stream_descriptor initial)events=gateway_complete_header command fault rows /\
  gateway_send_receipt io native readonly before world stream Ptrofs.zero initial(Vptr header Ptrofs.zero)112
    events after next(gateway_complete_header command fault rows) /\
  discipline None after next /\native next stream /\
  (forall object position,readonly object position->stable next object position).
Proof.
  intros SIDE PRIVATE STABLE INPUT COVER BYTES SEPARATE RUN.
  destruct(gateway_actual_send_producer backend io native stable discipline thread_errno runtime before world stream Ptrofs.zero
    initial(Vptr header Ptrofs.zero)112 readonly events after next SIDE PRIVATE STABLE INPUT
    ltac:(change Int64.max_unsigned with 18446744073709551615;lia)
    ltac:(right;exists header,Ptrofs.zero;split;[reflexivity|];split;
      [change(112<=18446744073709551616);lia|exact COVER])SEPARATE RUN)
    as[bytes[RECEIPT[FINAL[FINAL_PRIVATE FINAL_STABLE]]]].
  pose proof(@gateway_send_payload World Event io native readonly before world stream Ptrofs.zero initial(Vptr header Ptrofs.zero)112 events after next bytes RECEIPT)as PAYLOAD.
  destruct PAYLOAD as[[ZERO EMPTY]|[object[offset[POINTER CONTENT]]]];[lia|].
  inversion POINTER;subst object offset;change(Mem.loadbytes before header 0 112=Some(inj_bytes bytes))in CONTENT.
  assert(SAME:inj_bytes bytes=inj_bytes(gateway_complete_header command fault rows))by congruence.
  apply(f_equal proj_bytes)in SAME;rewrite !proj_inj_bytes in SAME;inversion SAME;subst bytes.
  split;[exact(@gateway_send_observed World Event io native readonly before world stream Ptrofs.zero initial(Vptr header Ptrofs.zero)112 events after next(gateway_complete_header command fault rows)RECEIPT)|].
  split;[exact RECEIPT|]. split;[exact FINAL|]. split;assumption.
Qed.
