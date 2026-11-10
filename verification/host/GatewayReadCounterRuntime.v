(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: A native counter update retains the actual read context. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewayReadContext GatewayThreadRuntime
  GatewayBufferReference GatewayReadCounterMemory GatewayReadyInterface.
Open Scope Z_scope.

Theorem gateway_read_counter_context {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    before world after stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_read_context native_private stable_readonly discipline None stream_block stream_offset initial
    data_block data_offset amount readonly before world ->
  Mem.store Mint64 before stream_block(Ptrofs.unsigned stream_offset+24)
    (Vlong(Int64.repr(Int64.unsigned(stream_remaining initial)-amount)))=Some after ->
  gateway_read_context native_private stable_readonly discipline None stream_block stream_offset(gateway_stream_debit initial amount)
    data_block data_offset amount readonly after world /\
  gateway_buffer_reference readonly stream_block data_block before after /\
  gateway_native_reference native_private before world after world.
Proof.
  intros[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]]STORE.
  pose proof(gateway_read_counter_retained before after stream_block stream_offset initial data_block data_offset amount readonly
    INPUT STORE)as RETAINED.
  split.
  - split.
    + eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact STREAM|exact STORE].
    + split;[exact STREAM|]. split;[exact DATA|]. split;[exact IMMUTABLE|].
      destruct INPUT as[CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
        READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
      constructor;try assumption.
      * eapply gateway_read_counter_cells;[exact STREAM_BOUND|exact CELLS|exact STORE].
      * intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply STREAM_PERM;exact RANGE].
      * eapply Mem.store_valid_block_1;[exact STORE|exact DATA_LIVE].
      * intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply DATA_PERM;exact RANGE].
      * intros object position HERE;eapply Mem.store_valid_block_1;
          [exact STORE|apply READONLY_LIVE with(position:=position);exact HERE].
      * intros object position HERE;eapply Mem.perm_unchanged_on;
          [exact RETAINED|left;exact HERE|apply READONLY_READABLE;exact HERE].
  - split.
    + split.
      * eapply Mem.unchanged_on_implies;[exact RETAINED|]. intros object position HERE LIVE;left;exact HERE.
      * intros object HERE position kind permission;split;intro PERMISSION;
          [eapply Mem.perm_store_1|eapply Mem.perm_store_2];eassumption.
    + intros object LIVE PRIVATE;split;[eapply Mem.store_valid_block_1;[exact STORE|exact LIVE]|exact PRIVATE].
Qed.
