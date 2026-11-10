(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Parser clients consume a source receipt, never a host-read axiom. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers Floats AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine.
Import ListNotations.
Open Scope Z_scope.

Record gateway_stream_values := {
  stream_descriptor : int;
  stream_control : int;
  stream_cancel_sent : int;
  stream_cli : int;
  stream_cancellation : val;
  stream_remaining : int64;
  stream_nodes : int64;
  stream_deadline : float
}.

Definition gateway_stream_slot block offset delta :=
  Vptr block(Ptrofs.add offset(Ptrofs.repr delta)).

Definition gateway_stream_memory memory block offset stream :Prop:=
  Mem.loadv Mint32 memory(gateway_stream_slot block offset 0)=Some(Vint(stream_descriptor stream)) /\
  Mem.loadv Mint32 memory(gateway_stream_slot block offset 4)=Some(Vint(stream_control stream)) /\
  Mem.loadv Mint32 memory(gateway_stream_slot block offset 8)=Some(Vint(stream_cancel_sent stream)) /\
  Mem.loadv Mint32 memory(gateway_stream_slot block offset 12)=Some(Vint(stream_cli stream)) /\
  Mem.loadv Mptr memory(gateway_stream_slot block offset 16)=Some(stream_cancellation stream) /\
  Mem.loadv Mint64 memory(gateway_stream_slot block offset 24)=Some(Vlong(stream_remaining stream)) /\
  Mem.loadv Mint64 memory(gateway_stream_slot block offset 32)=Some(Vlong(stream_nodes stream)) /\
  Mem.loadv Mfloat64 memory(gateway_stream_slot block offset 40)=Some(Vfloat(stream_deadline stream)).

Definition gateway_stream_read_after initial amount after :Prop:=
  stream_descriptor after=stream_descriptor initial /\stream_control after=stream_control initial /\
  stream_cli after=stream_cli initial /\stream_cancellation after=stream_cancellation initial /\
  stream_nodes after=stream_nodes initial /\stream_deadline after=stream_deadline initial /\
  stream_remaining after=Int64.repr(Int64.unsigned(stream_remaining initial)-amount) /\
  (stream_cancel_sent after=stream_cancel_sent initial \/stream_cancel_sent after=Int.one).

Definition gateway_stream_transport_after initial after :Prop:=
  stream_descriptor after=stream_descriptor initial /\stream_control after=stream_control initial /\
  stream_cli after=stream_cli initial /\stream_cancellation after=stream_cancellation initial /\
  stream_remaining after=stream_remaining initial /\stream_nodes after=stream_nodes initial /\
  stream_deadline after=stream_deadline initial /\
  (stream_cancel_sent after=stream_cancel_sent initial \/stream_cancel_sent after=Int.one).

Inductive gateway_native_io :=
| gateway_native_receive (descriptor:int)(requested:Z)(returned:Z)(bytes:list Byte.int)
| gateway_native_send (descriptor:int)(requested:Z)(returned:Z)(bytes:list Byte.int).

Definition gateway_received_event {Event}(io:Event->option gateway_native_io)
    (descriptor:int)(event:gateway_event Event) : list Byte.int:=
  match event with
  |gateway_primitive observed|gateway_committed_lost observed=>
    match io observed with
    |Some(gateway_native_receive actual _ _ bytes)=>if Int.eq actual descriptor then bytes else []
    |_=>[]
    end
  |_=>[]
  end.

Definition gateway_received_bytes {Event}(io:Event->option gateway_native_io)
    (descriptor:int)(events:list(gateway_event Event)) :list Byte.int:=
  flat_map(gateway_received_event io descriptor)events.

(* All native-input facts are raw initialized cells, actual permissions or pointer
   geometry. The client must derive them from real stack/malloc ownership. *)
Record gateway_read_inputs before stream_block stream_offset stream data_block data_offset amount
    (readonly:block->Z->Prop) :Prop:={
  gateway_read_stream_cells:gateway_stream_memory before stream_block stream_offset stream;
  gateway_read_amount:0<=amount<=Int64.max_unsigned;
  gateway_read_stream_bounds:Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus;
  gateway_read_data_bounds:Ptrofs.unsigned data_offset+amount<=Ptrofs.modulus;
  gateway_read_stream_owned:Mem.range_perm before stream_block(Ptrofs.unsigned stream_offset)
    (Ptrofs.unsigned stream_offset+48)Cur Writable;
  gateway_read_data_live:Mem.valid_block before data_block;
  gateway_read_data_owned:Mem.range_perm before data_block(Ptrofs.unsigned data_offset)
    (Ptrofs.unsigned data_offset+amount)Cur Writable;
  gateway_read_data_separate:stream_block<>data_block \/
    Ptrofs.unsigned data_offset+amount<=Ptrofs.unsigned stream_offset \/
    Ptrofs.unsigned stream_offset+48<=Ptrofs.unsigned data_offset;
  gateway_read_readonly_live:forall block position,readonly block position->Mem.valid_block before block;
  gateway_read_readonly_readable:forall block position,readonly block position->Mem.perm before block position Cur Readable;
  gateway_read_readonly_data:forall position,
    Ptrofs.unsigned data_offset<=position<Ptrofs.unsigned data_offset+amount->~readonly data_block position;
  gateway_read_readonly_remaining:forall position,
    Ptrofs.unsigned stream_offset+24<=position<Ptrofs.unsigned stream_offset+32->~readonly stream_block position;
  gateway_read_readonly_cancel:forall position,
    Ptrofs.unsigned stream_offset+8<=position<Ptrofs.unsigned stream_offset+12->~readonly stream_block position
}.

Record gateway_read_receipt {Event}(io:Event->option gateway_native_io)
    before stream_block stream_offset initial data_block data_offset amount
    (readonly:block->Z->Prop)(events:list(gateway_event Event))after(bytes:list Byte.int) :Prop:={
  gateway_read_count:Z.of_nat(length bytes)=amount;
  gateway_read_fits:amount<=Int64.unsigned(stream_remaining initial);
  gateway_read_observed:gateway_received_bytes io(stream_descriptor initial)events=bytes;
  gateway_read_initialized:Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)amount=
    Some(inj_bytes bytes);
  gateway_read_data_permissions:forall position kind permission,
    Ptrofs.unsigned data_offset<=position<Ptrofs.unsigned data_offset+amount ->
    (Mem.perm before data_block position kind permission<->Mem.perm after data_block position kind permission);
  gateway_read_stream_permissions:forall position kind permission,
    Ptrofs.unsigned stream_offset<=position<Ptrofs.unsigned stream_offset+48 ->
    (Mem.perm before stream_block position kind permission<->Mem.perm after stream_block position kind permission);
  gateway_read_final_stream:exists next,gateway_stream_memory after stream_block stream_offset next /\
    gateway_stream_read_after initial amount next;
  gateway_read_retained:Mem.unchanged_on readonly before after
}.

(* This type names an application source theorem to be supplied by GatewayTransfer,
   not an OS/runtime axiom. Generic parser clients may quantify over it while
   implementation is in progress; the integrated caller must instantiate it. *)
Definition gateway_read_source_producer {World Event}(backend:gateway_backend World Event)ge
    (io:Event->option gateway_native_io)(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(side:mem->World->Prop) :Prop:=
  forall before world stream_block stream_offset initial data_block data_offset amount readonly
      events after next,
    side before world ->
    native_private world stream_block ->native_private world data_block ->
    (forall block position,readonly block position->stable_readonly world block position) ->
    gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_read)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount)]Kstop before)world)
      events(gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
    exists bytes,gateway_read_receipt io before stream_block stream_offset initial data_block data_offset amount readonly events after bytes /\
      side after next /\native_private next stream_block /\native_private next data_block /\
      (forall block position,readonly block position->stable_readonly next block position) /\
      (forall block,Mem.valid_block before block->native_private world block->native_private next block) /\
      (forall block position,Mem.perm before block position Cur Readable->
        stable_readonly world block position->stable_readonly next block position).
