(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Rebuild actual read storage from the same completed transfer. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayStreamInterface GatewayReadContext GatewayThreadRuntime GatewayTransportFrame
  GatewayTransferState.
Open Scope Z_scope.

Theorem gateway_transfer_read_context {World}native_private stable_readonly discipline
    before world stream_block stream_offset initial data_block offset amount readonly after next :
  gateway_read_inputs before stream_block stream_offset initial data_block offset amount readonly ->
  @gateway_transfer_state World native_private stable_readonly discipline stream_block stream_offset data_block readonly
    initial after next ->
  gateway_transport_frame native_private readonly stream_block stream_offset data_block offset amount before world after next ->
  exists final,gateway_read_context native_private stable_readonly discipline None stream_block stream_offset final
    data_block offset amount readonly after next /\gateway_stream_transport_after initial final.
Proof.
  intros[CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL]
    [final[AFTER_CELLS[TRANSPORT[SIDE[STREAM[DATA[AFTER_LIVE IMMUTABLE]]]]]]]
    [FRAME STREAM_PERMISSIONS DATA_PERMISSIONS NATIVE].
  exists final;split;[|exact TRANSPORT].
  split;[exact SIDE|]. split;[exact STREAM|]. split;[exact DATA|]. split;[exact IMMUTABLE|].
  constructor;try assumption.
  - intros position RANGE;apply(proj1(STREAM_PERMISSIONS position Cur Writable RANGE));apply STREAM_PERM;exact RANGE.
  - intros position RANGE;apply(proj1(DATA_PERMISSIONS position Cur Writable RANGE));apply DATA_PERM;exact RANGE.
  - intros object position HERE;eapply Mem.valid_block_unchanged_on;
      [exact FRAME|apply READONLY_LIVE with(position:=position);exact HERE].
  - intros object position HERE;eapply Mem.perm_unchanged_on;
      [exact FRAME|exact HERE|apply READONLY_READABLE;exact HERE].
Qed.
