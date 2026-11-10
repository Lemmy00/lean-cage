(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Readiness is an application source producer over actual
   native-owned cells. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_data_region(data_block:Values.block)data_offset amount(block:Values.block)position :Prop:=
  block=data_block /\Ptrofs.unsigned data_offset<=position<Ptrofs.unsigned data_offset+amount.

(* The source caller supplies actual allocation/lifetime capabilities, rather than
   treating every writable block as disjoint from runtime and callback-owned state. *)
Definition gateway_ready_source_producer {World Event}(backend:gateway_backend World Event)ge
    (io:Event->option gateway_native_io)(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(side:mem->World->Prop):Prop:=
  forall before world stream_block stream_offset initial data_block data_offset amount readonly direction
      events after next,
    side before world ->native_private world stream_block ->native_private world data_block ->
    (forall block position,readonly block position->stable_readonly world block position) ->
    gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
    (direction=Int.repr 1 \/direction=Int.repr 4) ->
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint direction]Kstop before)world)
      events(gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
    exists final,
      gateway_read_inputs after stream_block stream_offset final data_block data_offset amount readonly /\
      gateway_stream_transport_after initial final /\
      Mem.unchanged_on(fun block position=>readonly block position \/
        gateway_data_region data_block data_offset amount block position)before after /\
      gateway_received_bytes io(stream_descriptor initial)events=[] /\
      side after next /\native_private next stream_block /\native_private next data_block /\
      (forall block position,readonly block position->stable_readonly next block position) /\
      (forall position kind permission,
        Ptrofs.unsigned stream_offset<=position<Ptrofs.unsigned stream_offset+48 ->
        (Mem.perm before stream_block position kind permission<->Mem.perm after stream_block position kind permission)) /\
      (forall block,Mem.valid_block before block->native_private world block->native_private next block) /\
      (forall block position,Mem.perm before block position Cur Readable->
        stable_readonly world block position->stable_readonly next block position).
