(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Payload writes retain the actual allocator header and parser slots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueRegions
  GatewayScalarLength GatewayScalarContext GatewayScalarBuffer GatewayNativeMemory GatewayHeapMemory GatewayStreamInterface
  GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_scalar_payload_readonly slots object size readonly candidate position :Prop:=
  readonly candidate position \/
  (candidate=gateway_value_tag_slot slots /\0<=position<8) \/
  (candidate=gateway_value_size_slot slots /\0<=position<8) \/
  (candidate=object /\(-8<=position<0 \/Int64.unsigned size<=position<Int64.unsigned size+1)).

Theorem gateway_scalar_payload_inputs {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object memory world :
  @gateway_scalar_buffer_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial
    readonly original size object memory world ->
  gateway_read_inputs memory stream_block stream_offset initial object Ptrofs.zero(Int64.unsigned size)
    (gateway_scalar_payload_readonly slots object size readonly).
Proof.
  intros[SIZED[HEAP[DIFFERENT[TAG_DIFFERENT[SIZE_DIFFERENT AVOIDS]]]]].
  destruct SIZED as[[[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN[TAG_SIZE[TAG_STREAM[SIZE_STREAM REST]]]]]]]]TAG_LOAD]SIZE_LOAD].
  destruct CONTEXT as[SIDE[STREAM[STABLE[INPUT INITIAL_FRAME]]]].
  destruct HEAP as[_[_[_[BOUND[HEADER OWNED]]]]].
  pose proof(Int64.unsigned_range size)as RANGE;constructor.
  - exact(gateway_value_stream_cells _ _ _ _ _ INPUT).
  - pose proof(Int64.unsigned_range_2 size);lia.
  - exact(gateway_value_stream_bounds _ _ _ _ _ INPUT).
  - change(0+Int64.unsigned size<=18446744073709551616);change Int64.modulus with 18446744073709551616 in RANGE;lia.
  - exact(gateway_value_stream_owned _ _ _ _ _ INPUT).
  - eapply Mem.perm_valid_block;apply(OWNED(-8));lia.
  - intros position REGION;eapply Mem.perm_implies;[apply OWNED;change(0<=position<Int64.unsigned size)in REGION;lia|constructor].
  - left;congruence.
  - intros candidate position[READ|[[SAME REGION]|[[SAME REGION]|[SAME REGION]]]].
    + exact(gateway_value_readonly_live _ _ _ _ _ INPUT candidate position READ).
    + subst candidate;eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia.
    + subst candidate;eapply Mem.perm_valid_block;apply(SIZE_OWN 0);lia.
    + subst candidate;eapply Mem.perm_valid_block;apply(OWNED(-8));lia.
  - intros candidate position[READ|[[SAME REGION]|[[SAME REGION]|[SAME REGION]]]].
    + exact(gateway_value_readonly_readable _ _ _ _ _ INPUT candidate position READ).
    + subst candidate;eapply Mem.perm_implies;[apply TAG_OWN;exact REGION|constructor].
    + subst candidate;eapply Mem.perm_implies;[apply SIZE_OWN;exact REGION|constructor].
    + subst candidate;eapply Mem.perm_implies;[apply OWNED;destruct REGION;lia|constructor].
  - intros position REGION[READ|[[SAME TAG_REGION]|[[SAME SIZE_REGION]|[SAME OUTSIDE]]]].
    + exact(AVOIDS position READ).
    + congruence.
    + congruence.
    + change(0<=position<Int64.unsigned size)in REGION;destruct OUTSIDE;lia.
  - intros position REGION[READ|[[SAME TAG_REGION]|[[SAME SIZE_REGION]|[SAME OUTSIDE]]]].
    + eapply gateway_value_readonly_counters;[exact INPUT| |exact READ];lia.
    + congruence.
    + congruence.
    + congruence.
  - intros position REGION[READ|[[SAME TAG_REGION]|[[SAME SIZE_REGION]|[SAME OUTSIDE]]]].
    + exact(gateway_value_readonly_cancel _ _ _ _ _ INPUT position REGION READ).
    + congruence.
    + congruence.
    + congruence.
Qed.

Theorem gateway_scalar_payload_stable {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots stream_block stream_offset initial readonly original size object memory world :
  gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object memory world ->
  forall candidate position,gateway_scalar_payload_readonly slots object size readonly candidate position ->stable world candidate position.
Proof.
  intros[SIZED[HEAP REST]]candidate position READ.
  destruct SIZED as[[[CONTEXT[TAG[SIZE SLOT_REST]]]TAG_LOAD]SIZE_LOAD].
  destruct CONTEXT as[SIDE[STREAM[STABLE INPUT]]].
  destruct HEAP as[_[PRIVATE HEAP_REST]].
  destruct READ as[READ|[[SAME RANGE]|[[SAME RANGE]|[SAME RANGE]]]].
  - exact(STABLE candidate position READ).
  - subst candidate;eapply gateway_thread_native_stable;eassumption.
  - subst candidate;eapply gateway_thread_native_stable;eassumption.
  - subst candidate;eapply gateway_thread_native_stable;eassumption.
Qed.
