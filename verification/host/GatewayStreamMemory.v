(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Only the actual private stream cells are protected from ambient
   writes. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayStreamInterface GatewayFrames GatewayWordsMemory.
Open Scope Z_scope.

Definition gateway_stream_region block offset:=gateway_byte_region block(Ptrofs.unsigned offset)48.

Lemma gateway_stream_slot_unsigned offset delta :
  0<=delta<48 ->Ptrofs.unsigned offset+48<=Ptrofs.modulus ->
  Ptrofs.unsigned(Ptrofs.add offset(Ptrofs.repr delta))=Ptrofs.unsigned offset+delta.
Proof.
  intros DELTA BOUND;pose proof(Ptrofs.unsigned_range offset)as RANGE.
  rewrite Ptrofs.add_unsigned.
  rewrite(Ptrofs.unsigned_repr delta)by(unfold Ptrofs.max_unsigned;lia).
  apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia.
Qed.

Lemma gateway_stream_cell_closed block offset delta chunk value :
  0<=delta ->delta+size_chunk chunk<=48 ->Ptrofs.unsigned offset+48<=Ptrofs.modulus ->
  gateway_region_closed(gateway_stream_region block offset)
    (fun memory=>Mem.loadv chunk memory(gateway_stream_slot block offset delta)=Some value).
Proof.
  intros DELTA WIDTH BOUND before after LOAD FRAME.
  assert(SMALL:0<=delta<48)by(pose proof(size_chunk_pos chunk);lia).
  unfold gateway_stream_slot,Mem.loadv in LOAD|-*.
  rewrite(gateway_stream_slot_unsigned _ _ SMALL BOUND)in LOAD|-*.
  destruct(zle(Ptrofs.unsigned offset+delta+size_chunk chunk)Ptrofs.modulus);[|lia].
  eapply Mem.load_unchanged_on;[exact FRAME| |exact LOAD].
  intros position RANGE;split;[reflexivity|]. change(Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+48);lia.
Qed.

Theorem gateway_stream_memory_closed block offset stream :
  Ptrofs.unsigned offset+48<=Ptrofs.modulus ->
  gateway_region_closed(gateway_stream_region block offset)
    (fun memory=>gateway_stream_memory memory block offset stream).
Proof.
  intros BOUND before after CELLS FRAME.
  destruct CELLS as[A[B[C[D[E[F[G H]]]]]]].
  assert(POINTER:size_chunk Mptr=8)by reflexivity.
  repeat split;eapply gateway_stream_cell_closed;try exact BOUND;try exact FRAME;
    try exact A;try exact B;try exact C;try exact D;try exact E;try exact F;try exact G;try exact H;
    rewrite ?POINTER;cbn[size_chunk];lia.
Qed.
