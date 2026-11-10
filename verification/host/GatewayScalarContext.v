(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Scalar guards read the same initialized tag, size and remaining cells. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayValueRegions GatewayScalarLength GatewayStreamMemory GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.

Lemma gateway_value_size_expression ge slots temporaries memory size :
  Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong size) ->
  expression_value ge(gateway_value_environment slots)temporaries memory(Evar _size tulong)(Vlong size).
Proof.
  intro LOAD;apply location_read_value with(b:=gateway_value_size_slot slots)(ofs:=Ptrofs.zero).
  - apply local_location_value;unfold gateway_value_environment;apply PTree.gss.
  - apply deref_loc_value with(chunk:=Mint64);[reflexivity|exact LOAD].
Qed.

Definition gateway_value_sized {World}native stable discipline scalar slots stream_block stream_offset initial readonly original
    size memory world :Prop:=
  @gateway_value_tagged World native stable discipline slots stream_block stream_offset initial readonly original
    (Int64.repr(gateway_scalar_code scalar))memory world /\
  Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong size).

Theorem gateway_value_sized_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    scalar slots stream_block stream_offset initial readonly original size :
  gateway_ambient_closed backend(gateway_value_sized native stable discipline scalar slots stream_block stream_offset
    initial readonly original size).
Proof.
  intros before world after next[TAGGED LOAD]INTERFERENCE;split.
  - eapply gateway_value_tagged_ambient;[exact runtime|exact TAGGED|exact INTERFERENCE].
  - destruct TAGGED as[[[SIDE CONTEXT][TAG_NATIVE[SIZE_NATIVE REST]]]TAG_LOAD].
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)as[_[_ FRAME]].
    change(Mem.load Mint64 before(gateway_value_size_slot slots)0=Some(Vlong size))in LOAD.
    change(Mem.load Mint64 after(gateway_value_size_slot slots)0=Some(Vlong size)).
    eapply Mem.load_unchanged_on;[exact FRAME| |exact LOAD].
    intros position RANGE;split;[left;exact SIZE_NATIVE|unfold gateway_native_no_output;tauto].
Qed.

Lemma gateway_sized_remaining {World}native stable discipline scalar slots stream_block stream_offset initial readonly original
    size memory world :
  @gateway_value_sized World native stable discipline scalar slots stream_block stream_offset initial readonly original size memory world ->
  Mem.loadv Mint64 memory(gateway_stream_slot stream_block stream_offset 24)=Some(Vlong(stream_remaining initial)).
Proof.
  intros[[[[SIDE[STREAM[READONLY[INPUT FRAME]]]]REST]TAG]SIZE].
  destruct(gateway_value_stream_cells _ _ _ _ _ INPUT)as(A&B&C&D&E&F&G&H);exact F.
Qed.
