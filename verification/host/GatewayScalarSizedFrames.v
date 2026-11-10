(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Parser cells need only their exact disjoint frame across native operations. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueRegions
  GatewayScalarLength GatewayScalarContext GatewayScalarBuffer GatewayScalarPayloadMemory GatewayScalarTerminate
  GatewayStreamInterface GatewayThreadRuntime.
Open Scope Z_scope.

Theorem gateway_value_sized_frame_effect {World}native stable discipline scalar slots stream_block stream_offset initial readonly original size
    before world after next :
  @gateway_value_sized World native stable discipline scalar slots stream_block stream_offset initial readonly original size before world ->
  discipline None after next ->gateway_access_retained native stable before world next ->
  Mem.unchanged_on(gateway_value_sized_region slots stream_block stream_offset readonly)before after ->
  gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size after next.
Proof.
  intros[[[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]]TAG_LOAD]SIZE_LOAD]NEXT_SIDE[RETAIN_NATIVE RETAIN_STABLE]FRAME.
  destruct CONTEXT as[SIDE[STREAM[STABLE[INPUT INITIAL_FRAME]]]].
  assert(INPUT_FRAME:Mem.unchanged_on(gateway_value_input_region stream_block stream_offset readonly)before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption]. }
  split.
  - split.
    + split.
      * split;[exact NEXT_SIDE|]. split.
        -- apply RETAIN_NATIVE;[|exact STREAM]. eapply Mem.perm_valid_block.
           apply(gateway_value_stream_owned _ _ _ _ _ INPUT(Ptrofs.unsigned stream_offset));lia.
        -- split.
           ++ intros candidate position READ;apply RETAIN_STABLE;
                [exact(gateway_value_readonly_readable _ _ _ _ _ INPUT candidate position READ)|apply STABLE;exact READ].
           ++ split.
              ** eapply gateway_value_inputs_frame;eassumption.
              ** eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|].
                 eapply Mem.unchanged_on_implies;[exact INPUT_FRAME|intros;right;assumption].
      * split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia|exact TAG]|].
        split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(SIZE_OWN 0);lia|exact SIZE]|].
        split;[intros position RANGE;eapply Mem.perm_unchanged_on;
          [exact FRAME|right;left;split;[reflexivity|exact RANGE]|apply TAG_OWN;exact RANGE]|].
        split;[|exact REST]. intros position RANGE;eapply Mem.perm_unchanged_on;
          [exact FRAME|right;right;split;[reflexivity|exact RANGE]|apply SIZE_OWN;exact RANGE].
    + change(Mem.load Mint64 after(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_scalar_code scalar)))).
      change(Mem.load Mint64 before(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_scalar_code scalar))))in TAG_LOAD.
      eapply Mem.load_unchanged_on;[exact FRAME|intros;right;left;split;[reflexivity|exact H]|exact TAG_LOAD].
  - change(Mem.load Mint64 after(gateway_value_size_slot slots)0=Some(Vlong size)).
    change(Mem.load Mint64 before(gateway_value_size_slot slots)0=Some(Vlong size))in SIZE_LOAD.
    eapply Mem.load_unchanged_on;[exact FRAME|intros;right;right;split;[reflexivity|exact H]|exact SIZE_LOAD].
Qed.


Lemma gateway_value_sized_rebase {World}native stable discipline replacement scalar slots stream_block stream_offset initial readonly original size
    memory world :
  @gateway_value_sized World native stable discipline scalar slots stream_block stream_offset initial readonly original size memory world ->
  replacement None memory world ->
  gateway_value_sized native stable replacement scalar slots stream_block stream_offset initial readonly original size memory world.
Proof.
  intros[[[[SIDE[STREAM[STABLE[INPUT FRAME]]]]SLOTS]TAG]SIZE]NEXT_SIDE.
  split;[split;[split;[|exact SLOTS]|exact TAG]|exact SIZE].
  split;[exact NEXT_SIDE|]. split;[exact STREAM|]. split;[exact STABLE|]. split;assumption.
Qed.

Theorem gateway_scalar_buffer_rebase {World}native stable discipline replacement heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object memory world :
  @gateway_scalar_buffer_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object memory world ->replacement None memory world ->
  gateway_scalar_buffer_ready native stable replacement heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object memory world.
Proof.
  intros[SIZED[[_[PRIVATE[ORIGIN HEAP]]]SEPARATE]]NEXT_SIDE;split.
  - eapply gateway_value_sized_rebase;eassumption.
  - split;[|exact SEPARATE]. split;[exact NEXT_SIDE|]. split;[exact PRIVATE|]. split;assumption.
Qed.

Theorem gateway_scalar_terminated_rebase {World}native stable discipline replacement heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes memory world :
  @gateway_scalar_terminated_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world ->replacement None memory world ->
  gateway_scalar_terminated_ready native stable replacement heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world.
Proof.
  intros[[BUFFER PAYLOAD]TERMINATED]NEXT_SIDE.
  split;[split;[|exact PAYLOAD]|exact TERMINATED].
  eapply gateway_scalar_buffer_rebase;eassumption.
Qed.

Lemma gateway_scalar_terminated_side {World}native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world :
  @gateway_scalar_terminated_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world ->discipline None memory world.
Proof. intros[[[_[[SIDE HEAP]SEPARATE]]PAYLOAD]TERMINATED];exact SIDE. Qed.
