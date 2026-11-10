(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A completed payload read retains the same freeable scalar allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueRegions
  GatewayScalarLength GatewayScalarContext GatewayScalarBuffer GatewayScalarReadMemory GatewayNativeMemory GatewayHeapMemory
  GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_scalar_payload_receipt {World Event}(io:Event->option gateway_native_io)
    native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original size object
    before world reading after next bytes :
  @gateway_scalar_buffer_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial
    readonly original size object before world ->
  gateway_read_receipt io before stream_block stream_offset initial object Ptrofs.zero(Int64.unsigned size)
    (gateway_scalar_payload_readonly slots object size readonly)reading after bytes ->
  discipline None after next ->native next stream_block ->native next object ->
  (forall candidate position,gateway_scalar_payload_readonly slots object size readonly candidate position ->stable next candidate position) ->
  gateway_access_retained native stable before world next ->
  exists final_stream,gateway_stream_read_after initial(Int64.unsigned size)final_stream /\
    gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset final_stream
      readonly original size object after next.
Proof.
  intros[SIZED[HEAP SEPARATE]]RECEIPT AFTER_SIDE AFTER_STREAM AFTER_OBJECT AFTER_STABLE[RETAIN_NATIVE RETAIN_STABLE].
  destruct SIZED as[[[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN SLOT_REST]]]]]TAG_LOAD]SIZE_LOAD].
  destruct CONTEXT as[SIDE[STREAM[STABLE[INPUT INITIAL_FRAME]]]].
  destruct HEAP as[HEAP_SIDE[OBJECT[ORIGIN[BOUND[HEADER OWNED]]]]].
  destruct RECEIPT as[COUNT FITS OBSERVED INITIALIZED DATA_PERMS STREAM_PERMS FINAL_STREAM FRAME].
  destruct FINAL_STREAM as[final_stream[CELLS READ_AFTER]].
  assert(TAG_FRAME:Mem.unchanged_on(fun candidate position=>candidate=gateway_value_tag_slot slots /\0<=position<8)before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|intros;right;left;assumption]. }
  assert(SIZE_FRAME:Mem.unchanged_on(fun candidate position=>candidate=gateway_value_size_slot slots /\0<=position<8)before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|intros;right;right;left;assumption]. }
  assert(READ_FRAME:Mem.unchanged_on readonly before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption]. }
  exists final_stream;split;[exact READ_AFTER|]. split.
  - split.
    + split.
      * split.
        -- split;[exact AFTER_SIDE|]. split;[exact AFTER_STREAM|]. split.
           ++ intros candidate position READ;apply AFTER_STABLE;left;exact READ.
           ++ split.
              ** constructor.
                 --- exact CELLS.
                 --- exact(gateway_value_stream_bounds _ _ _ _ _ INPUT).
                 --- intros position RANGE;apply(proj1(STREAM_PERMS position Cur Writable RANGE));apply(gateway_value_stream_owned _ _ _ _ _ INPUT);exact RANGE.
                 --- intros candidate position READ;eapply Mem.valid_block_unchanged_on;[exact READ_FRAME|].
                     exact(gateway_value_readonly_live _ _ _ _ _ INPUT candidate position READ).
                 --- intros candidate position READ;eapply Mem.perm_unchanged_on;[exact READ_FRAME|exact READ|].
                     exact(gateway_value_readonly_readable _ _ _ _ _ INPUT candidate position READ).
                 --- exact(gateway_value_readonly_cancel _ _ _ _ _ INPUT).
                 --- exact(gateway_value_readonly_counters _ _ _ _ _ INPUT).
              ** eapply Mem.unchanged_on_trans;eassumption.
        -- split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia|exact TAG]|].
           split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(SIZE_OWN 0);lia|exact SIZE]|].
           split;[intros position RANGE;eapply Mem.perm_unchanged_on;[exact TAG_FRAME|split;[reflexivity|exact RANGE]|apply TAG_OWN;exact RANGE]|].
           split;[|exact SLOT_REST]. intros position RANGE;eapply Mem.perm_unchanged_on;
             [exact SIZE_FRAME|split;[reflexivity|exact RANGE]|apply SIZE_OWN;exact RANGE].
      * change(Mem.load Mint64 after(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_scalar_code scalar)))).
        change(Mem.load Mint64 before(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_scalar_code scalar))))in TAG_LOAD.
        eapply Mem.load_unchanged_on;[exact TAG_FRAME|intros;split;[reflexivity|exact H]|exact TAG_LOAD].
    + change(Mem.load Mint64 after(gateway_value_size_slot slots)0=Some(Vlong size)).
      change(Mem.load Mint64 before(gateway_value_size_slot slots)0=Some(Vlong size))in SIZE_LOAD.
      eapply Mem.load_unchanged_on;[exact SIZE_FRAME|intros;split;[reflexivity|exact H]|exact SIZE_LOAD].
  - split;[|exact SEPARATE]. split;[exact AFTER_SIDE|]. split;[exact AFTER_OBJECT|]. split;[exact ORIGIN|].
    split;[exact BOUND|]. split.
    + eapply Mem.load_unchanged_on;[exact FRAME| |exact HEADER].
      intros position RANGE;right;right;right;split;[reflexivity|left;cbn[size_chunk]in RANGE;lia].
    + intros position RANGE;destruct(Z_le_gt_dec 0 position)as[POSITIVE|NEGATIVE];
        destruct(Z_lt_ge_dec position(Int64.unsigned size))as[PREFIX|SUFFIX].
      * apply(proj1(DATA_PERMS position Cur Freeable ltac:(change(0<=position<Int64.unsigned size);lia)));apply OWNED;exact RANGE.
      * eapply Mem.perm_unchanged_on;[exact FRAME|right;right;right;split;[reflexivity|right;lia]|apply OWNED;exact RANGE].
      * eapply Mem.perm_unchanged_on;[exact FRAME|right;right;right;split;[reflexivity|left;lia]|apply OWNED;exact RANGE].
      * lia.
Qed.
