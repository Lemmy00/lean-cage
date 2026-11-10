(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Couple actual buffer lifetime, initialized cells and thread state. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayStreamInterface GatewayStreamMemory
  GatewayReadyInterface GatewayReadMemory GatewayThreadRuntime GatewayWordsMemory.
Open Scope Z_scope.

Definition gateway_read_context {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(discipline:option val->mem->World->Prop)mode
    stream_block stream_offset initial data_block data_offset amount readonly(memory:mem)(world:World):Prop:=
  discipline mode memory world /\native_private world stream_block /\native_private world data_block /\
  (forall block position,readonly block position->stable_readonly world block position) /\
  gateway_read_inputs memory stream_block stream_offset initial data_block data_offset amount readonly.

Theorem gateway_read_context_preserved {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    mode stream_block stream_offset initial data_block data_offset amount readonly before world after next :
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly before world ->
  discipline mode after next ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly after next.
Proof.
  intros[SIDE[STREAM_PRIVATE[DATA_PRIVATE[IMMUTABLE INPUT]]]]SIDE_AFTER[NATIVE STABLE]FRAME.
  assert(UNCHANGED:Mem.unchanged_on
    (gateway_read_region stream_block stream_offset data_block data_offset amount readonly)before after).
  { eapply gateway_native_frame_restrict;[exact FRAME| |].
    - intros block position[STREAM|[DATA|READONLY]].
      + destruct STREAM as[SAME RANGE];subst block;left;exact STREAM_PRIVATE.
      + destruct DATA as[SAME RANGE];subst block;left;exact DATA_PRIVATE.
      + right;apply IMMUTABLE;exact READONLY.
    - intros block position HERE NONE;exact NONE. }
  split;[exact SIDE_AFTER|]. split.
  - apply NATIVE;[eapply gateway_read_stream_live;exact INPUT|exact STREAM_PRIVATE].
  - split.
    + apply NATIVE;[exact(gateway_read_data_live _ _ _ _ _ _ _ _ INPUT)|exact DATA_PRIVATE].
    + split.
      * intros block position READONLY;apply STABLE.
        -- exact(gateway_read_readonly_readable _ _ _ _ _ _ _ _ INPUT block position READONLY).
        -- apply IMMUTABLE;exact READONLY.
      * eapply gateway_read_inputs_unchanged;[exact INPUT|exact UNCHANGED].
Qed.

Theorem gateway_read_context_ambient {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    mode stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_runtime_discipline backend
    (gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
      data_block data_offset amount readonly).
Proof.
  intros before world after next CONTEXT INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode before world after next
    (proj1 CONTEXT)INTERFERENCE)as[SIDE[ACCESS FRAME]].
  eapply gateway_read_context_preserved;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME].
Qed.
