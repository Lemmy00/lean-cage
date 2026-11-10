(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Request sends retain the real caller's byte span. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewaySendRuntime
  GatewayThreadRuntime GatewayTransportFrame.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_send_inputs before stream_block stream_offset initial readonly:=
  gateway_read_inputs before stream_block stream_offset initial stream_block stream_offset 0 readonly.
Definition gateway_payload_cells(readonly:block->Z->Prop)(pointer:val)(amount:Z):Prop:=
  amount=0 \/exists object offset,pointer=Vptr object offset /\
    Ptrofs.unsigned offset+amount<=Ptrofs.modulus /\
    forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+amount->readonly object position.
Definition gateway_sent_payload before(pointer:val)(amount:Z)(bytes:list Byte.int):Prop:=
  amount=0 /\bytes=[] \/exists object offset,pointer=Vptr object offset /\
    Mem.loadbytes before object(Ptrofs.unsigned offset)amount=Some(inj_bytes bytes).

Record gateway_send_receipt {World Event}(io:Event->option gateway_native_io)
    (native:World->block->Prop)readonly before world stream_block stream_offset initial pointer amount
    events after next(bytes:list Byte.int):Prop:={
  gateway_send_count:Z.of_nat(length bytes)=amount;
  gateway_send_observed:gateway_sent_bytes io(stream_descriptor initial)events=bytes;
  gateway_send_payload:gateway_sent_payload before pointer amount bytes;
  gateway_send_final_stream:exists final,gateway_stream_memory after stream_block stream_offset final /\
    gateway_stream_transport_after initial final;
  gateway_send_frame:gateway_transport_frame native readonly stream_block stream_offset
    stream_block stream_offset 0 before world after next
}.

(* The final caller supplies this application-source theorem from the actual
   maintained transfer body; it is not an OS send or helper-success axiom. *)
Definition gateway_send_source_producer {World Event}(backend:gateway_backend World Event)ge
    (io:Event->option gateway_native_io)(native:World->block->Prop)
    (stable:World->block->Z->Prop)(side:mem->World->Prop):Prop:=
  forall before world stream_block stream_offset initial pointer amount readonly events after next,
    side before world->native world stream_block->
    (forall object position,readonly object position->stable world object position)->
    gateway_send_inputs before stream_block stream_offset initial readonly->
    0<=amount<=Int64.max_unsigned->gateway_payload_cells readonly pointer amount->
    stream_descriptor initial<>stream_control initial->
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_transfer)
        [Vptr stream_block stream_offset;pointer;Vlong(Int64.repr amount);Vint Int.one]Kstop before)world)
      events(gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
    exists bytes,gateway_send_receipt io native readonly before world stream_block stream_offset initial pointer amount
      events after next bytes /\side after next /\native next stream_block /\
      (forall object position,readonly object position->stable next object position).
