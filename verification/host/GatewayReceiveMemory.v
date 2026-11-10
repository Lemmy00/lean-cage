(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: A real receive changes only its initialized destination prefix. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayStreamInterface GatewayStreamMemory GatewayReadMemory
  GatewayReadContext GatewayThreadRuntime.
Open Scope Z_scope.

Theorem gateway_receive_read_inputs {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)before world after
    stream_block stream_offset initial data_block data_offset amount readonly chunk written :
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
  native_private world stream_block ->native_private world data_block ->
  (forall block position,readonly block position->stable_readonly world block position) ->
  0<=written<=chunk ->chunk<=amount ->
  gateway_native_permissions before after data_block data_offset chunk ->
  gateway_native_frame native_private stable_readonly(gateway_native_region data_block data_offset written)
    world before after ->
  gateway_read_inputs after stream_block stream_offset initial data_block data_offset amount readonly /\
  Mem.unchanged_on(fun block position=>gateway_stream_region stream_block stream_offset block position \/
    readonly block position)before after /\
  gateway_native_permissions before after data_block data_offset amount.
Proof.
  intros INPUT STREAM_PRIVATE DATA_PRIVATE IMMUTABLE WRITTEN CHUNK PERMISSIONS FRAME.
  assert(STREAM_DISJOINT:forall block position,gateway_stream_region stream_block stream_offset block position ->
    ~gateway_native_region data_block data_offset written block position).
  { intros block position[SAME RANGE][SAME_DATA DATA_RANGE];subst block.
    change(Ptrofs.unsigned stream_offset<=position<Ptrofs.unsigned stream_offset+48)in RANGE.
    destruct(gateway_read_data_separate _ _ _ _ _ _ _ _ INPUT)as[DIFFERENT|[BEFORE|AFTER]];
      [congruence|lia|lia]. }
  assert(READONLY_DISJOINT:forall block position,readonly block position ->
    ~gateway_native_region data_block data_offset written block position).
  { intros block position HERE[SAME RANGE];subst block.
    eapply(gateway_read_readonly_data _ _ _ _ _ _ _ _ INPUT position);[lia|exact HERE]. }
  assert(PROTECTED:Mem.unchanged_on
    (fun block position=>gateway_stream_region stream_block stream_offset block position \/readonly block position)
    before after).
  { eapply gateway_native_frame_restrict;[exact FRAME| |].
    - intros block position[STREAM|READONLY].
      + destruct STREAM as[SAME RANGE];subst block;left;exact STREAM_PRIVATE.
      + right;apply IMMUTABLE;exact READONLY.
    - intros block position[STREAM|READONLY];
        [apply STREAM_DISJOINT;exact STREAM|apply READONLY_DISJOINT;exact READONLY]. }
  assert(DATA_PERMISSIONS:gateway_native_permissions before after data_block data_offset amount).
  { intros position kind permission RANGE.
    destruct(Z_lt_ge_dec position(Ptrofs.unsigned data_offset+chunk))as[IN|OUT].
    - apply PERMISSIONS;lia.
    - apply(Mem.unchanged_on_perm _ _ _ FRAME data_block position kind permission).
      + split;[left;exact DATA_PRIVATE|]. intro OUTPUT;destruct OUTPUT as[SAME BOUND];lia.
      + exact(gateway_read_data_live _ _ _ _ _ _ _ _ INPUT). }
  split.
  - destruct INPUT as[CELLS AMOUNT STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
      READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
    constructor.
    + eapply gateway_stream_memory_closed;[exact STREAM_BOUND|exact CELLS|].
      eapply Mem.unchanged_on_implies;[exact PROTECTED|]. intros block position HERE;left;exact HERE.
    + exact AMOUNT.
    + exact STREAM_BOUND.
    + exact DATA_BOUND.
    + intros position RANGE;eapply Mem.perm_unchanged_on;[exact PROTECTED| |apply STREAM_PERM;exact RANGE].
      left;split;[reflexivity|]. change(Ptrofs.unsigned stream_offset<=position<Ptrofs.unsigned stream_offset+48);exact RANGE.
    + eapply Mem.valid_block_unchanged_on;[exact FRAME|exact DATA_LIVE].
    + intros position RANGE;apply(proj1(DATA_PERMISSIONS position Cur Writable RANGE));apply DATA_PERM;exact RANGE.
    + exact SEPARATE.
    + intros block position HERE;eapply Mem.valid_block_unchanged_on;
        [exact PROTECTED|apply READONLY_LIVE with(position:=position);exact HERE].
    + intros block position HERE;eapply Mem.perm_unchanged_on;
        [exact PROTECTED|right;exact HERE|apply READONLY_READABLE;exact HERE].
    + exact READONLY_DATA.
    + exact READONLY_REMAINING.
    + exact READONLY_CANCEL.
  - split;assumption.
Qed.

Theorem gateway_receive_read_context {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    mode before world after next stream_block stream_offset initial data_block data_offset amount readonly chunk written :
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly before world ->
  discipline mode after next ->gateway_access_retained native_private stable_readonly before world next ->
  0<=written<=chunk ->chunk<=amount ->
  gateway_native_permissions before after data_block data_offset chunk ->
  gateway_native_frame native_private stable_readonly(gateway_native_region data_block data_offset written)
    world before after ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly after next /\
  Mem.unchanged_on(fun block position=>gateway_stream_region stream_block stream_offset block position \/
    readonly block position)before after /\
  gateway_native_permissions before after data_block data_offset amount.
Proof.
  intros[SIDE[STREAM_PRIVATE[DATA_PRIVATE[IMMUTABLE INPUT]]]]AFTER[NATIVE STABLE]WRITTEN CHUNK PERMISSIONS FRAME.
  destruct(gateway_receive_read_inputs native_private stable_readonly before world after
    stream_block stream_offset initial data_block data_offset amount readonly chunk written
    INPUT STREAM_PRIVATE DATA_PRIVATE IMMUTABLE WRITTEN CHUNK PERMISSIONS FRAME)as[INPUT_AFTER[PROTECTED DATA_PERMS]].
  split;[|split;assumption].
  split;[exact AFTER|]. split.
  - apply NATIVE;[eapply gateway_read_stream_live;exact INPUT|exact STREAM_PRIVATE].
  - split.
    + apply NATIVE;[exact(gateway_read_data_live _ _ _ _ _ _ _ _ INPUT)|exact DATA_PRIVATE].
    + split;[|exact INPUT_AFTER]. intros block position HERE;apply STABLE.
      * exact(gateway_read_readonly_readable _ _ _ _ _ _ _ _ INPUT block position HERE).
      * apply IMMUTABLE;exact HERE.
Qed.
