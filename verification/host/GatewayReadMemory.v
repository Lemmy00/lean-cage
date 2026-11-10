(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Raw read inputs are retained only over their actual protected byte regions. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayStreamInterface GatewayStreamMemory GatewayReadyInterface
  GatewayFrames GatewayWordsMemory.
Open Scope Z_scope.

Definition gateway_read_region stream_block stream_offset data_block data_offset amount readonly
    (block:Values.block)(position:Z):Prop:=
  gateway_stream_region stream_block stream_offset block position \/
  gateway_data_region data_block data_offset amount block position \/readonly block position.

Theorem gateway_read_inputs_unchanged before after stream_block stream_offset initial data_block data_offset
    amount readonly :
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
  Mem.unchanged_on(gateway_read_region stream_block stream_offset data_block data_offset amount readonly)before after ->
  gateway_read_inputs after stream_block stream_offset initial data_block data_offset amount readonly.
Proof.
  intros[CELLS AMOUNT STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL]FRAME.
  constructor.
  - eapply gateway_stream_memory_closed;[exact STREAM_BOUND|exact CELLS|].
    eapply Mem.unchanged_on_implies;[exact FRAME|]. intros block position HERE;left;exact HERE.
  - exact AMOUNT.
  - exact STREAM_BOUND.
  - exact DATA_BOUND.
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply STREAM_PERM;exact RANGE].
    left;split;[reflexivity|]. change(Ptrofs.unsigned stream_offset<=position<Ptrofs.unsigned stream_offset+48);exact RANGE.
  - eapply Mem.valid_block_unchanged_on;[exact FRAME|exact DATA_LIVE].
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply DATA_PERM;exact RANGE].
    right;left;split;[reflexivity|exact RANGE].
  - exact SEPARATE.
  - intros block position READONLY;eapply Mem.valid_block_unchanged_on;
      [exact FRAME|apply READONLY_LIVE with(position:=position);exact READONLY].
  - intros block position READONLY;eapply Mem.perm_unchanged_on;
      [exact FRAME|right;right;exact READONLY|apply READONLY_READABLE;exact READONLY].
  - exact READONLY_DATA.
  - exact READONLY_REMAINING.
  - exact READONLY_CANCEL.
Qed.

Lemma gateway_read_stream_live before stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
  Mem.valid_block before stream_block.
Proof.
  intro INPUT;eapply Mem.perm_valid_block.
  apply(gateway_read_stream_owned _ _ _ _ _ _ _ _ INPUT(Ptrofs.unsigned stream_offset));lia.
Qed.
