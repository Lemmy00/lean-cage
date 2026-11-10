(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Header construction and request sends share the real initialized stream. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayStreamMemory GatewayStreamRelations
  GatewayReadMemory GatewayReadContext GatewaySendState GatewaySendInterface GatewayTransportFrame GatewayCallerBuffers GatewayCallerFamily
  GatewaySpawnResources GatewaySpawnActions GatewayPostSpawnContext GatewayPostSpawnCleanup GatewayHeaderRuntime GatewayHeaderPacket.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_header_readonly(readonly:block->Z->Prop)stream object position:Prop:=
  readonly object position \/object=stream /\0<=position<48.
Definition gateway_request_readonly(readonly:block->Z->Prop)header object position:Prop:=
  readonly object position \/object=header /\0<=position<112.

Theorem gateway_header_inputs_from_parent {World}native stable discipline resources builders genuine readonly selected reference owner
    data control stream header data_left data_right control_left control_right leases before world:
  gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner data control
    data_left data_right control_left control_right postspawn_empty_builders leases before world->
  selected stream->selected header->Mem.range_perm reference stream 0 48 Cur Freeable->
  (forall object position,readonly object position->Mem.perm reference object position Cur Readable)->
  @gateway_header_resources World native stable discipline None header[stream](gateway_header_readonly readonly stream)before world before world.
Proof.
  intros[SIDE VALID GENUINE BUILDERS FAMILY DATA CONTROL LEASES]STREAM HEADER STREAM_RANGE READABLE.
  destruct(FAMILY header HEADER)as[HEADER_LIVE[HEADER_PRIVATE[READONLY[HEADER_FRAME HISTORY]]]].
  destruct(FAMILY stream STREAM)as[STREAM_LIVE[STREAM_PRIVATE[STREAM_READONLY[[STREAM_FRAME STREAM_PERMISSIONS]REST]]]].
  apply gateway_header_resources_initial;try assumption.
  - intros object[HERE|ABSENT];[subst object;split;assumption|contradiction].
  - intros object position[OLD|[SAME RANGE]].
    + destruct(READONLY object position OLD)as[LIVE[PRIVATE|[ACTUAL STABLE]]];split.
      * eapply Mem.perm_unchanged_on;[exact(proj1 HEADER_FRAME)|exact OLD|apply READABLE;exact OLD].
      * left;exact PRIVATE.
      * exact ACTUAL.
      * right;exact STABLE.
    + subst object;split;[|left;exact STREAM_PRIVATE].
      eapply Mem.perm_implies.
      * apply(proj1(STREAM_PERMISSIONS stream(or_introl eq_refl)position Cur Freeable));apply STREAM_RANGE;exact RANGE.
      * constructor.
Qed.

Section Send.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
  (runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variables(readonly:Values.block->Z->Prop)(stream header:Values.block)(initial:gateway_stream_values)
  (before:mem)(world:World)(bytes:list Byte.int)(after:mem)(next:World).
Hypotheses(PACKET:gateway_header_packet native stable discipline None header[stream](gateway_header_readonly readonly stream)
    before world bytes after next)
  (CELLS:gateway_stream_memory before stream Ptrofs.zero initial)
  (WRITABLE:Mem.range_perm before stream 0 48 Cur Writable)
  (STREAM_HEADER:stream<>header)(STREAM_READONLY:forall position,~readonly stream position).

Theorem gateway_request_send_inputs:
  gateway_send_inputs after stream Ptrofs.zero initial(gateway_request_readonly readonly header) /\
  discipline None after next /\native next stream /\
  (forall object position,gateway_request_readonly readonly header object position->stable next object position).
Proof.
  destruct PACKET as[RESOURCES HEADER_WRITABLE LENGTH BYTES].
  pose proof RESOURCES as COPY;destruct COPY as[SIDE HEADER_PRIVATE HEADER_LIVE HELD READONLY FRAME PERMISSIONS NATIVE STABLE].
  destruct(HELD stream ltac:(left;reflexivity))as[STREAM_LIVE STREAM_PRIVATE].
  assert(STREAM_FRAME:Mem.unchanged_on(gateway_stream_region stream Ptrofs.zero)before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|]. intros object position[SAME RANGE]LIVE.
    right;split;[exact SAME|exact RANGE]. }
  assert(AFTER_CELLS:gateway_stream_memory after stream Ptrofs.zero initial).
  { eapply gateway_stream_memory_closed;[change(48<=18446744073709551616);lia|exact CELLS|exact STREAM_FRAME]. }
  assert(REQUEST_READABLE:forall object position,gateway_request_readonly readonly header object position->
    Mem.perm after object position Cur Readable).
  { intros object position[OLD|[SAME RANGE]].
    - exact(proj1(READONLY object position(or_introl OLD))).
    - subst object;eapply Mem.perm_implies;[apply HEADER_WRITABLE;exact RANGE|constructor]. }
  split.
  - constructor.
    + exact AFTER_CELLS.
    + change(0<=0<=18446744073709551615);lia.
    + change(48<=18446744073709551616);lia.
    + change(0<=18446744073709551616);lia.
    + intros position RANGE;eapply Mem.perm_unchanged_on;[exact STREAM_FRAME| |apply WRITABLE;exact RANGE].
      split;[reflexivity|exact RANGE].
    + exact STREAM_LIVE.
    + intros position RANGE;cbn in RANGE;lia.
    + right;left;change(0<=0);lia.
    + intros object position HERE;eapply Mem.perm_valid_block;apply REQUEST_READABLE;exact HERE.
    + exact REQUEST_READABLE.
    + intros position RANGE;cbn in RANGE;lia.
    + intros position RANGE[OLD|[SAME HEADER_RANGE]];[exact(STREAM_READONLY position OLD)|congruence].
    + intros position RANGE[OLD|[SAME HEADER_RANGE]];[exact(STREAM_READONLY position OLD)|congruence].
  - split;[exact SIDE|]. split;[exact STREAM_PRIVATE|].
    intros object position[OLD|[SAME RANGE]].
    + destruct(proj2(READONLY object position(or_introl OLD)))as[PRIVATE|IMMUTABLE];[|exact IMMUTABLE].
      exact(gateway_thread_native_stable _ _ _ _ _ _ runtime None after next object position SIDE PRIVATE).
    + subst object;exact(gateway_thread_native_stable _ _ _ _ _ _ runtime None after next header position SIDE HEADER_PRIVATE).
Qed.
End Send.
