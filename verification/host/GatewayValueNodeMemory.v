(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real writable node cell is debited without changing other stream fields. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayStreamInterface GatewayStreamMemory GatewayValueEntry.
Open Scope Z_scope.

Definition gateway_stream_node_debit initial :gateway_stream_values:={|
  stream_descriptor:=stream_descriptor initial;stream_control:=stream_control initial;
  stream_cancel_sent:=stream_cancel_sent initial;stream_cli:=stream_cli initial;
  stream_cancellation:=stream_cancellation initial;stream_remaining:=stream_remaining initial;
  stream_nodes:=Int64.sub(stream_nodes initial)Int64.one;stream_deadline:=stream_deadline initial|}.

Lemma gateway_value_node_access memory stream_block stream_offset initial readonly :
  gateway_value_inputs memory stream_block stream_offset initial readonly ->
  Mem.valid_access memory Mint64 stream_block(Ptrofs.unsigned stream_offset+32)Writable.
Proof.
  intro INPUT;pose proof(gateway_value_stream_cells _ _ _ _ _ INPUT)as[_[_[_[_[_[_[COUNTER REST]]]]]]].
  unfold gateway_stream_slot,Mem.loadv in COUNTER.
  rewrite(gateway_stream_slot_unsigned stream_offset 32 ltac:(lia)
    (gateway_value_stream_bounds _ _ _ _ _ INPUT))in COUNTER.
  destruct(zle(Ptrofs.unsigned stream_offset+32+size_chunk Mint64)Ptrofs.modulus);[|discriminate].
  destruct(Mem.load_valid_access _ _ _ _ _ COUNTER)as[READABLE ALIGNMENT].
  split;[|exact ALIGNMENT].
  intros position RANGE;apply(gateway_value_stream_owned _ _ _ _ _ INPUT position);cbn[size_chunk]in RANGE;lia.
Qed.

Lemma gateway_value_node_allocate memory stream_block stream_offset initial readonly :
  gateway_value_inputs memory stream_block stream_offset initial readonly ->
  exists after,Mem.store Mint64 memory stream_block(Ptrofs.unsigned stream_offset+32)
    (Vlong(Int64.sub(stream_nodes initial)Int64.one))=Some after.
Proof.
  intro INPUT;destruct(Mem.valid_access_store memory Mint64 stream_block(Ptrofs.unsigned stream_offset+32)
    (Vlong(Int64.sub(stream_nodes initial)Int64.one))(gateway_value_node_access _ _ _ _ _ INPUT))
    as[after STORE];exists after;exact STORE.
Qed.

Lemma gateway_value_node_other memory after stream_block stream_offset initial delta chunk value :
  0<=delta<48 ->delta+size_chunk chunk<=48 ->(delta+size_chunk chunk<=32 \/40<=delta) ->
  Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->
  Mem.store Mint64 memory stream_block(Ptrofs.unsigned stream_offset+32)
    (Vlong(Int64.sub(stream_nodes initial)Int64.one))=Some after ->
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

Theorem gateway_value_node_cells memory after stream_block stream_offset initial :
  Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->gateway_stream_memory memory stream_block stream_offset initial ->
  Mem.store Mint64 memory stream_block(Ptrofs.unsigned stream_offset+32)
    (Vlong(Int64.sub(stream_nodes initial)Int64.one))=Some after ->
  gateway_stream_memory after stream_block stream_offset(gateway_stream_node_debit initial).
Proof.
  intros BOUND[A[B[C[D[E[F[G H]]]]]]]STORE.
  assert(POINTER:size_chunk Mptr=8)by reflexivity.
  repeat split;cbn[gateway_stream_node_debit];try(eapply gateway_value_node_other;
    [lia|rewrite ?POINTER;cbn[size_chunk];lia|rewrite ?POINTER;cbn[size_chunk];lia|exact BOUND|exact STORE|eassumption]).
  unfold gateway_stream_slot,Mem.loadv.
  rewrite(gateway_stream_slot_unsigned stream_offset 32 ltac:(lia)BOUND).
  destruct(zle(Ptrofs.unsigned stream_offset+32+size_chunk Mint64)Ptrofs.modulus);[|cbn[size_chunk]in*;lia].
  erewrite Mem.load_store_same by exact STORE;reflexivity.
Qed.

Theorem gateway_value_node_inputs memory after stream_block stream_offset initial readonly :
  gateway_value_inputs memory stream_block stream_offset initial readonly ->
  Mem.store Mint64 memory stream_block(Ptrofs.unsigned stream_offset+32)
    (Vlong(Int64.sub(stream_nodes initial)Int64.one))=Some after ->
  gateway_value_inputs after stream_block stream_offset(gateway_stream_node_debit initial)readonly /\
    Mem.unchanged_on readonly memory after.
Proof.
  intros INPUT STORE.
  assert(FRAME:Mem.unchanged_on readonly memory after).
  { eapply Mem.store_unchanged_on;[exact STORE|]. intros position RANGE READ.
    eapply(gateway_value_readonly_counters _ _ _ _ _ INPUT position);[cbn[size_chunk]in RANGE;lia|exact READ]. }
  split;[|exact FRAME].
  destruct INPUT as[CELLS BOUND OWNED LIVE READABLE CANCEL COUNTERS].
  constructor;try assumption.
  - eapply gateway_value_node_cells;eassumption.
  - intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply OWNED;exact RANGE].
  - intros object position READ;eapply Mem.store_valid_block_1;[exact STORE|apply LIVE with(position:=position);exact READ].
  - intros object position READ;eapply Mem.perm_store_1;[exact STORE|apply READABLE;exact READ].
Qed.

Lemma gateway_stream_node_decreases initial :stream_nodes initial<>Int64.zero ->
  Int64.unsigned(stream_nodes(gateway_stream_node_debit initial))=Int64.unsigned(stream_nodes initial)-1.
Proof.
  intro NONZERO;change(Int64.unsigned(Int64.repr(Int64.unsigned(stream_nodes initial)-1))=
    Int64.unsigned(stream_nodes initial)-1).
  rewrite Int64.unsigned_repr.
  - reflexivity.
  - pose proof(Int64.unsigned_range(stream_nodes initial)).
    assert(NONZERO_UNSIGNED:Int64.unsigned(stream_nodes initial)<>0).
    { intro ZERO;apply NONZERO;rewrite<-(Int64.repr_unsigned(stream_nodes initial)),ZERO;reflexivity. }
    unfold Int64.max_unsigned;lia.
Qed.
