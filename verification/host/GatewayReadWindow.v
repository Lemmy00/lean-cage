(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Partial receive acknowledgments retain a genuine smaller destination. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayStreamInterface GatewayReadContext.
Open Scope Z_scope.

Lemma gateway_read_advanced_offset offset size count :
  0<=size<=Int64.max_unsigned ->0<=count<size ->Ptrofs.unsigned offset+size<=Ptrofs.modulus ->
  Ptrofs.unsigned(Ptrofs.add offset(Ptrofs.repr count))=Ptrofs.unsigned offset+count.
Proof.
  intros SIZE COUNT BOUND;unfold Ptrofs.add.
  rewrite(Ptrofs.unsigned_repr count)by(change Ptrofs.max_unsigned with 18446744073709551615;
    change Int64.max_unsigned with 18446744073709551615 in SIZE;lia).
  apply Ptrofs.unsigned_repr.
  pose proof(Ptrofs.unsigned_range offset).
  change Ptrofs.max_unsigned with 18446744073709551615.
  change Ptrofs.modulus with 18446744073709551616 in BOUND;lia.
Qed.

Theorem gateway_read_advance_inputs memory stream_block stream_offset initial data_block data_offset size readonly count :
  gateway_read_inputs memory stream_block stream_offset initial data_block data_offset size readonly ->
  0<count<size ->
  gateway_read_inputs memory stream_block stream_offset initial data_block
    (Ptrofs.add data_offset(Ptrofs.repr count))(size-count)readonly.
Proof.
  intros INPUT COUNT.
  pose proof(gateway_read_advanced_offset data_offset size count
    (gateway_read_amount _ _ _ _ _ _ _ _ INPUT)ltac:(lia)
    (gateway_read_data_bounds _ _ _ _ _ _ _ _ INPUT))as OFFSET.
  destruct INPUT as[CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
  constructor.
  - exact CELLS.
  - lia.
  - exact STREAM_BOUND.
  - rewrite OFFSET;lia.
  - exact STREAM_PERM.
  - exact DATA_LIVE.
  - rewrite OFFSET;intros position RANGE;apply DATA_PERM;lia.
  - rewrite OFFSET;destruct SEPARATE as[DIFFERENT|[BEFORE|AFTER]];
      [left;exact DIFFERENT|right;left;lia|right;right;lia].
  - exact READONLY_LIVE.
  - exact READONLY_READABLE.
  - rewrite OFFSET;intros position RANGE;apply READONLY_DATA;lia.
  - exact READONLY_REMAINING.
  - exact READONLY_CANCEL.
Qed.

Theorem gateway_read_advance_context {World}native_private stable_readonly discipline mode
    stream_block stream_offset initial data_block data_offset size readonly count memory world :
  @gateway_read_context World native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset size readonly memory world ->0<count<size ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block(Ptrofs.add data_offset(Ptrofs.repr count))(size-count)readonly memory world.
Proof.
  intros[SIDE[STREAM[DATA[READONLY INPUT]]]]COUNT.
  split;[exact SIDE|]. split;[exact STREAM|]. split;[exact DATA|]. split;[exact READONLY|].
  eapply gateway_read_advance_inputs;[exact INPUT|exact COUNT].
Qed.
