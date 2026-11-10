(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Individual readonly native effects retain the actual scalar buffer. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueRegions
  GatewayScalarLength GatewayScalarContext GatewayScalarBuffer GatewayScalarPayloadMemory GatewayScalarTerminate
  GatewayScalarFrames GatewayNativeMemory GatewayHeapMemory GatewayStreamInterface GatewayThreadRuntime.
Open Scope Z_scope.

Theorem gateway_scalar_terminated_native_effect {World}native stable discipline heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object bytes before world after next:
  @gateway_scalar_terminated_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial
    readonly original size object bytes before world ->discipline None after next ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_scalar_terminated_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial
    readonly original size object bytes after next.
Proof.
  intros[[[SIZED[[SIDE[PRIVATE[ORIGIN BLOCK]]]SEPARATE]][COUNT LOAD]]TERMINATED]AFTER_SIDE ACCESS FRAME.
  assert(HEAP_FRAME:Mem.unchanged_on(gateway_heap_region object(Int64.unsigned size+1))before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros candidate position[SAME RANGE]LIVE;subst candidate;split;[left;exact PRIVATE|unfold gateway_native_no_output;tauto]. }
  assert(LIVE:Mem.valid_block before object).
  { destruct BLOCK as[BOUND[HEADER PERMISSIONS]];eapply Mem.perm_valid_block;apply(PERMISSIONS(-8));lia. }
  split.
  - split.
    + split;[eapply gateway_value_sized_effect;[exact SIZED|exact AFTER_SIDE|exact ACCESS|exact FRAME]|].
      split;[|exact SEPARATE]. split;[exact AFTER_SIDE|]. split;[apply(proj1 ACCESS);assumption|].
      split;[exact ORIGIN|eapply gateway_heap_block_frame;[exact BLOCK|exact HEAP_FRAME]].
    + split;[exact COUNT|]. eapply Mem.loadbytes_unchanged_on;[exact HEAP_FRAME| |exact LOAD].
      intros position RANGE;split;[reflexivity|change(0<=position<Int64.unsigned size)in RANGE;lia].
  - eapply Mem.loadbytes_unchanged_on;[exact HEAP_FRAME| |exact TERMINATED].
    intros position RANGE;split;[reflexivity|change(0<=position<Int64.unsigned size+1)in RANGE;lia].
Qed.
