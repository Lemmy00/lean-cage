(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Scalar payloads retain their bytes through the actual terminator store. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueRegions
  GatewayScalarLength GatewayScalarContext GatewayScalarBuffer GatewayNativeMemory GatewayHeapMemory GatewayStreamInterface
  GatewayThreadRuntime GatewayWordsMemory.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_scalar_payload_ready {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes memory world :Prop:=
  @gateway_scalar_buffer_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object memory world /\Z.of_nat(length bytes)=Int64.unsigned size /\
    Mem.loadbytes memory object 0(Int64.unsigned size)=Some(inj_bytes bytes).

Lemma gateway_scalar_payload_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes :
  GatewayOperations.gateway_runtime_discipline backend(gateway_scalar_payload_ready native stable discipline heap_allocation scalar
    slots stream_block stream_offset initial readonly original size object bytes).
Proof.
  intros before world after next[READY[COUNT BYTES]]INTERFERENCE;split.
  - eapply gateway_scalar_buffer_ambient;[exact runtime|exact READY|exact INTERFERENCE].
  - split;[exact COUNT|].
    destruct READY as[SIZED[[SIDE[PRIVATE HEAP]]REST]].
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)as[_[_ FRAME]].
    eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact BYTES].
    intros position RANGE;split;[left;exact PRIVATE|unfold gateway_native_no_output;tauto].
Qed.

Definition gateway_value_sized_region slots stream_block stream_offset readonly candidate position :Prop:=
  gateway_value_input_region stream_block stream_offset readonly candidate position \/
  gateway_byte_region(gateway_value_tag_slot slots)0 8 candidate position \/
  gateway_byte_region(gateway_value_size_slot slots)0 8 candidate position.

Lemma gateway_value_sized_memory_frame {World}native stable discipline scalar slots stream_block stream_offset initial readonly original
    size before world after :
  @gateway_value_sized World native stable discipline scalar slots stream_block stream_offset initial readonly original size before world ->
  discipline None after world ->
  Mem.unchanged_on(gateway_value_sized_region slots stream_block stream_offset readonly)before after ->
  gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size after world.
Proof.
  intros[[[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]]TAG_LOAD]SIZE_LOAD]NEXT_SIDE FRAME.
  destruct CONTEXT as[SIDE[STREAM[STABLE[INPUT INITIAL_FRAME]]]].
  assert(INPUT_FRAME:Mem.unchanged_on(gateway_value_input_region stream_block stream_offset readonly)before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption]. }
  split.
  - split.
    + split.
      * split;[exact NEXT_SIDE|]. split;[exact STREAM|]. split;[exact STABLE|]. split.
        -- eapply gateway_value_inputs_frame;eassumption.
        -- eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|].
           eapply Mem.unchanged_on_implies;[exact INPUT_FRAME|intros;right;assumption].
      * split;[exact TAG|]. split;[exact SIZE|].
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

Theorem gateway_scalar_buffer_terminate {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes before world after :
  gateway_scalar_payload_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world ->
  Mem.store Mint8signed before object(Int64.unsigned size)(Vint Int.zero)=Some after ->
  gateway_scalar_payload_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes after world /\Mem.loadbytes after object 0(Int64.unsigned size+1)=Some(inj_bytes(bytes++[Byte.zero])).
Proof.
  intros[READY[COUNT BYTES]]STORE.
  destruct READY as[SIZED[HEAP[DIFFERENT[TAG_DIFFERENT[SIZE_DIFFERENT AVOIDS]]]]].
  pose proof HEAP as[SIDE[PRIVATE[ORIGIN[BOUND[HEADER OWNED]]]]].
  assert(NEXT_SIDE:discipline None after world).
  { eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact PRIVATE|exact STORE]. }
  assert(PARSER_FRAME:Mem.unchanged_on(gateway_value_sized_region slots stream_block stream_offset readonly)before after).
  { eapply Mem.store_unchanged_on;[exact STORE|].
    intros position RANGE[[[SAME STREAM_RANGE]|READ]|[[SAME TAG_RANGE]|[SAME SIZE_RANGE]]];
      try congruence;exact(AVOIDS position READ). }
  assert(PREFIX:Mem.loadbytes after object 0(Int64.unsigned size)=Some(inj_bytes bytes)).
  { erewrite Mem.loadbytes_store_other;[exact BYTES|exact STORE|right;right;left;lia]. }
  split.
  - split.
    + split;[eapply gateway_value_sized_memory_frame;[exact SIZED|exact NEXT_SIDE|exact PARSER_FRAME]|].
      split;[|split;[exact DIFFERENT|split;[exact TAG_DIFFERENT|split;[exact SIZE_DIFFERENT|exact AVOIDS]]]].
      split;[exact NEXT_SIDE|]. split;[exact PRIVATE|]. split;[exact ORIGIN|]. split;[exact BOUND|]. split.
      * erewrite Mem.load_store_other;[exact HEADER|exact STORE|right;left;cbn[size_chunk];pose proof(Int64.unsigned_range size);lia].
      * intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply OWNED;exact RANGE].
    + split;assumption.
  - assert(SUFFIX:Mem.loadbytes after object(Int64.unsigned size)1=Some(inj_bytes[Byte.zero])).
    { exact(Mem.loadbytes_store_same _ _ _ _ _ _ STORE). }
    unfold inj_bytes;rewrite map_app;eapply Mem.loadbytes_concat;
      [exact PREFIX|exact SUFFIX|pose proof(Int64.unsigned_range size);lia|lia].
Qed.
