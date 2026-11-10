(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Successive real sends retain the same caller bytes and stream. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayThreadRuntime GatewayStreamInterface GatewayStreamRelations
  GatewaySendInterface GatewayReadContext GatewayReadMemory GatewayTransportFrame GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_send_frame_inputs {World}native readonly before world after next stream offset initial final:
  gateway_send_inputs before stream offset initial readonly->
  gateway_stream_memory after stream offset final->
  @gateway_transport_frame World native readonly stream offset stream offset 0 before world after next->
  gateway_send_inputs after stream offset final readonly.
Proof.
  intros INPUT CELLS[FRAME PERMISSIONS DATA NATIVE].
  destruct INPUT as[OLD AMOUNT STREAM_BOUND DATA_BOUND STREAM_OWNED DATA_LIVE DATA_OWNED SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
  constructor;try assumption.
  - intros position RANGE;apply(PERMISSIONS position Cur Writable RANGE);apply STREAM_OWNED;exact RANGE.
  - eapply Mem.valid_block_unchanged_on;[exact FRAME|exact DATA_LIVE].
  - intros position RANGE;lia.
  - intros object position HERE;eapply Mem.valid_block_unchanged_on;[exact FRAME|apply READONLY_LIVE with(position:=position);exact HERE].
  - intros object position HERE;eapply Mem.perm_unchanged_on;[exact FRAME|exact HERE|apply READONLY_READABLE;exact HERE].
Qed.

Definition gateway_sending_state {World}native stable discipline stream readonly reference origin original memory world:Prop:=
  exists current,
    @gateway_read_context World native stable discipline None stream Ptrofs.zero current stream Ptrofs.zero 0 readonly memory world /\
    gateway_stream_transport_after original current /\
    gateway_transport_frame native readonly stream Ptrofs.zero stream Ptrofs.zero 0 reference origin memory world.

Lemma gateway_sending_after {World Event}(io:Event->option gateway_native_io)native stable discipline stream readonly reference origin original current
    before world pointer amount events after next bytes:
  @gateway_sending_state World native stable discipline stream readonly reference origin original before world->
  gateway_send_inputs before stream Ptrofs.zero current readonly->
  gateway_stream_transport_after original current->
  gateway_send_receipt io native readonly before world stream Ptrofs.zero current pointer amount events after next bytes->
  discipline None after next->native next stream->
  (forall object position,readonly object position->stable next object position)->
  gateway_sending_state native stable discipline stream readonly reference origin original after next.
Proof.
  intros[old[RAW[TRANSPORT HISTORY]]]INPUT CURRENT RECEIPT SIDE PRIVATE STABLE.
  destruct RECEIPT as[COUNT OBSERVED PAYLOAD[final[CELLS FINAL_TRANSPORT]]FRAME].
  exists final;split.
  - split;[exact SIDE|]. split;[exact PRIVATE|]. split;[exact PRIVATE|]. split;[exact STABLE|].
    eapply gateway_send_frame_inputs;[exact INPUT|exact CELLS|exact FRAME].
  - split;[eapply gateway_transport_transitive;[exact CURRENT|exact FINAL_TRANSPORT]|].
    eapply gateway_transport_frame_transitive;[exact HISTORY|exact FRAME].
Qed.

Lemma gateway_sending_preserved {World}native stable discipline stream readonly reference origin original
    before world after next:
  @gateway_sending_state World native stable discipline stream readonly reference origin original before world->
  discipline None after next->gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_sending_state native stable discipline stream readonly reference origin original after next.
Proof.
  intros[current[RAW[TRANSPORT HISTORY]]]SIDE ACCESS FRAME.
  assert(LOCAL:gateway_transport_frame native readonly stream Ptrofs.zero stream Ptrofs.zero 0 before world after next).
  { constructor.
    - eapply gateway_native_frame_restrict;[exact FRAME| |].
      + intros object position HERE;right;apply(proj1(proj2(proj2(proj2 RAW))));exact HERE.
      + intros object position HERE BAD;exact BAD.
    - intros position kind permission RANGE;apply(Mem.unchanged_on_perm _ _ _ FRAME stream position kind permission).
      + split;[left;exact(proj1(proj2 RAW))|intro BAD;exact BAD].
      + eapply gateway_read_stream_live;exact(proj2(proj2(proj2(proj2 RAW)))).
    - intros position kind permission RANGE;cbn in RANGE;lia.
    - eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]. }
  exists current;split.
  - eapply gateway_read_context_preserved;[exact RAW|exact SIDE|exact ACCESS|exact FRAME].
  - split;[exact TRANSPORT|eapply gateway_transport_frame_transitive;[exact HISTORY|exact LOCAL]].
Qed.

Lemma gateway_sending_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    stream readonly reference origin original:
  gateway_runtime_discipline backend
    (gateway_sending_state native stable discipline stream readonly reference origin original).
Proof.
  intros before world after next GOOD INTERFERENCE.
  destruct GOOD as[current[RAW[TRANSPORT HISTORY]]].
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next(proj1 RAW)INTERFERENCE)
    as[SIDE[ACCESS FRAME]].
  eapply gateway_sending_preserved;[exists current;split;[exact RAW|split;assumption]|exact SIDE|exact ACCESS|exact FRAME].
Qed.
