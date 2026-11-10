(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual remaining-field store preserves initialized read bytes. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayStreamInterface GatewayStreamMemory GatewayReadyInterface GatewayReadMemory.
Open Scope Z_scope.

Definition gateway_stream_debit initial amount :gateway_stream_values:={|
  stream_descriptor:=stream_descriptor initial;stream_control:=stream_control initial;
  stream_cancel_sent:=stream_cancel_sent initial;stream_cli:=stream_cli initial;
  stream_cancellation:=stream_cancellation initial;
  stream_remaining:=Int64.repr(Int64.unsigned(stream_remaining initial)-amount);
  stream_nodes:=stream_nodes initial;stream_deadline:=stream_deadline initial|}.

Lemma gateway_stream_debit_relation initial amount :
  gateway_stream_read_after initial amount(gateway_stream_debit initial amount).
Proof. repeat split;try reflexivity;left;reflexivity. Qed.

Lemma gateway_read_counter_valid memory stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_read_inputs memory stream_block stream_offset initial data_block data_offset amount readonly ->
  Mem.valid_access memory Mint64 stream_block(Ptrofs.unsigned stream_offset+24)Writable.
Proof.
  intro INPUT.
  pose proof(gateway_read_stream_cells _ _ _ _ _ _ _ _ INPUT)as[_[_[_[_[_[COUNTER REST]]]]]].
  unfold gateway_stream_slot,Mem.loadv in COUNTER.
  rewrite(gateway_stream_slot_unsigned stream_offset 24 ltac:(lia)
    (gateway_read_stream_bounds _ _ _ _ _ _ _ _ INPUT))in COUNTER.
  destruct(zle(Ptrofs.unsigned stream_offset+24+size_chunk Mint64)Ptrofs.modulus);[|discriminate].
  pose proof(Mem.load_valid_access _ _ _ _ _ COUNTER)as[READABLE ALIGNMENT].
  split;[|exact ALIGNMENT].
  intros position RANGE;apply(gateway_read_stream_owned _ _ _ _ _ _ _ _ INPUT position);cbn[size_chunk]in RANGE;lia.
Qed.

Lemma gateway_read_counter_allocate memory stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_read_inputs memory stream_block stream_offset initial data_block data_offset amount readonly ->
  exists after,Mem.store Mint64 memory stream_block(Ptrofs.unsigned stream_offset+24)
    (Vlong(Int64.repr(Int64.unsigned(stream_remaining initial)-amount)))=Some after.
Proof.
  intro INPUT;destruct(Mem.valid_access_store memory Mint64 stream_block(Ptrofs.unsigned stream_offset+24)
    (Vlong(Int64.repr(Int64.unsigned(stream_remaining initial)-amount)))
    (gateway_read_counter_valid memory stream_block stream_offset initial data_block data_offset amount readonly INPUT))
    as[after STORE]. exists after;exact STORE.
Qed.

Lemma gateway_read_counter_other memory after stream_block stream_offset initial amount delta chunk value :
  0<=delta<48 ->delta+size_chunk chunk<=48 ->(delta+size_chunk chunk<=24 \/32<=delta) ->
  Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->
  Mem.store Mint64 memory stream_block(Ptrofs.unsigned stream_offset+24)
    (Vlong(Int64.repr(Int64.unsigned(stream_remaining initial)-amount)))=Some after ->
  Mem.loadv chunk memory(gateway_stream_slot stream_block stream_offset delta)=Some value ->
  Mem.loadv chunk after(gateway_stream_slot stream_block stream_offset delta)=Some value.
Proof.
  intros DELTA WIDTH SEPARATE BOUND STORE LOAD.
  unfold gateway_stream_slot,Mem.loadv in LOAD|-*.
  rewrite(gateway_stream_slot_unsigned stream_offset delta DELTA BOUND)in LOAD|-*.
  destruct(zle(Ptrofs.unsigned stream_offset+delta+size_chunk chunk)Ptrofs.modulus);[|lia].
  erewrite Mem.load_store_other;[exact LOAD|exact STORE|].
  right;destruct SEPARATE;[left|right];cbn[size_chunk];lia.
Qed.

Theorem gateway_read_counter_cells memory after stream_block stream_offset initial amount :
  Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->gateway_stream_memory memory stream_block stream_offset initial ->
  Mem.store Mint64 memory stream_block(Ptrofs.unsigned stream_offset+24)
    (Vlong(Int64.repr(Int64.unsigned(stream_remaining initial)-amount)))=Some after ->
  gateway_stream_memory after stream_block stream_offset(gateway_stream_debit initial amount).
Proof.
  intros BOUND[A[B[C[D[E[F[G H]]]]]]]STORE.
  assert(POINTER:size_chunk Mptr=8)by reflexivity.
  repeat split;cbn[gateway_stream_debit];try(eapply gateway_read_counter_other;
    [lia|rewrite ?POINTER;cbn[size_chunk];lia|rewrite ?POINTER;cbn[size_chunk];lia|exact BOUND|exact STORE|eassumption]).
  unfold gateway_stream_slot,Mem.loadv.
  rewrite(gateway_stream_slot_unsigned stream_offset 24 ltac:(lia)BOUND).
  destruct(zle(Ptrofs.unsigned stream_offset+24+size_chunk Mint64)Ptrofs.modulus);[|cbn[size_chunk]in*;lia].
  erewrite Mem.load_store_same by exact STORE;reflexivity.
Qed.

Theorem gateway_read_counter_retained memory after stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_read_inputs memory stream_block stream_offset initial data_block data_offset amount readonly ->
  Mem.store Mint64 memory stream_block(Ptrofs.unsigned stream_offset+24)
    (Vlong(Int64.repr(Int64.unsigned(stream_remaining initial)-amount)))=Some after ->
  Mem.unchanged_on(fun object position=>readonly object position \/
    gateway_data_region data_block data_offset amount object position)memory after.
Proof.
  intros INPUT STORE;eapply Mem.store_unchanged_on;[exact STORE|].
  intros position RANGE[READONLY|[SAME DATA_RANGE]].
  - eapply(gateway_read_readonly_remaining _ _ _ _ _ _ _ _ INPUT position);[cbn[size_chunk]in RANGE;lia|exact READONLY].
  - destruct(gateway_read_data_separate _ _ _ _ _ _ _ _ INPUT)as[DIFFERENT|[BEFORE|AFTER]];
      [congruence|cbn[size_chunk]in RANGE;lia|cbn[size_chunk]in RANGE;lia].
Qed.
