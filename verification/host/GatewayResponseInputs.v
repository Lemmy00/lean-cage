(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Reply storage comes from the same live native caller allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayStreamInterface GatewayReadContext GatewaySendState GatewayTransportFrame
  GatewayHeaderRuntime GatewayHeaderPacket GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_response_readonly(readonly:block->Z->Prop)response object position:=
  readonly object position /\object<>response.

Theorem gateway_packet_response_allocation {World}native stable discipline mode header held readonly original owner bytes before world response:
  @gateway_header_packet World native stable discipline mode header held readonly original owner bytes before world->
  native owner response->Mem.range_perm original response 0 24 Cur Writable->
  (forall position,0<=position<24->readonly response position)->
  native world response /\Mem.range_perm before response 0 24 Cur Writable.
Proof.
  intros[RESOURCES WRITABLE LENGTH BYTES]PRIVATE RANGE INCLUDED.
  destruct RESOURCES as[SIDE HEADER_PRIVATE HEADER_LIVE HELD RO FRAME PERMISSIONS NATIVE STABLE].
  assert(LIVE:Mem.valid_block original response).
  { eapply Mem.perm_valid_block;apply(RANGE 0);lia. }
  destruct(NATIVE response LIVE PRIVATE)as[AFTER_LIVE AFTER_NATIVE].
  split;[exact AFTER_NATIVE|]. intros position INSIDE.
  eapply Mem.perm_unchanged_on;[exact FRAME|apply INCLUDED;exact INSIDE|apply RANGE;exact INSIDE].
Qed.

Theorem gateway_sending_response_context {World}native stable discipline stream response readonly reference owner original before world:
  stream<>response->native owner response->Mem.range_perm reference response 0 24 Cur Writable->
  (forall position,0<=position<24->readonly response position)->
  @gateway_sending_state World native stable discipline stream readonly reference owner original before world->
  exists current,gateway_read_context native stable discipline None stream Ptrofs.zero current response Ptrofs.zero 24
    (gateway_response_readonly readonly response)before world /\gateway_stream_transport_after original current.
Proof.
  intros SEPARATE PRIVATE RANGE INCLUDED[current[RAW[TRANSPORT[FRAME STREAM_PERM DATA_PERM NATIVE]]]].
  destruct RAW as[SIDE[STREAM_NATIVE[IGNORED[IMMUTABLE INPUT]]]].
  assert(LIVE:Mem.valid_block reference response).
  { eapply Mem.perm_valid_block;apply(RANGE 0);lia. }
  destruct(NATIVE response LIVE PRIVATE)as[RESPONSE_LIVE RESPONSE_NATIVE].
  exists current;split;[|exact TRANSPORT].
  split;[exact SIDE|]. split;[exact STREAM_NATIVE|]. split;[exact RESPONSE_NATIVE|]. split.
  - intros object position[HERE DIFFERENT];apply IMMUTABLE;exact HERE.
  - constructor.
    + exact(gateway_read_stream_cells _ _ _ _ _ _ _ _ INPUT).
    + change(0<=24<=18446744073709551615);lia.
    + exact(gateway_read_stream_bounds _ _ _ _ _ _ _ _ INPUT).
    + change(24<=18446744073709551616);lia.
    + exact(gateway_read_stream_owned _ _ _ _ _ _ _ _ INPUT).
    + exact RESPONSE_LIVE.
    + intros position INSIDE;eapply Mem.perm_unchanged_on;[exact FRAME|apply INCLUDED;exact INSIDE|apply RANGE;exact INSIDE].
    + left;exact SEPARATE.
    + intros object position[HERE DIFFERENT];eapply gateway_read_readonly_live;[exact INPUT|exact HERE].
    + intros object position[HERE DIFFERENT];eapply gateway_read_readonly_readable;[exact INPUT|exact HERE].
    + intros position INSIDE[HERE DIFFERENT];apply DIFFERENT;reflexivity.
    + intros position INSIDE[HERE DIFFERENT];eapply gateway_read_readonly_remaining;[exact INPUT|exact INSIDE|exact HERE].
    + intros position INSIDE[HERE DIFFERENT];eapply gateway_read_readonly_cancel;[exact INPUT|exact INSIDE|exact HERE].
Qed.
