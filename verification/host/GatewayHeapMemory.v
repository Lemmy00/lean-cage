(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real allocation retains its logical allocator origin and live permissions. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayNativeMemory GatewayThreadRuntime GatewayStreamInterface GatewayOperations.
Open Scope Z_scope.

Lemma gateway_heap_block_frame before after object amount :
  gateway_heap_block before object amount ->Mem.unchanged_on(gateway_heap_region object amount)before after ->
  gateway_heap_block after object amount.
Proof.
  intros[BOUND[HEADER OWNED]]FRAME;split;[exact BOUND|]. split.
  - eapply Mem.load_unchanged_on;[exact FRAME| |exact HEADER].
    intros position RANGE;split;[reflexivity|cbn[size_chunk]in RANGE;lia].
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|split;[reflexivity|exact RANGE]|].
    apply OWNED;exact RANGE.
Qed.

Definition gateway_heap_context {World}(native:World->block->Prop)(discipline:option val->mem->World->Prop)
    (heap_allocation:block->Z->Prop)mode object amount memory world :Prop:=
  discipline mode memory world /\native world object /\heap_allocation object amount /\gateway_heap_block memory object amount.

Theorem gateway_heap_context_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)heap_allocation mode object amount :
  gateway_runtime_discipline backend(gateway_heap_context native discipline heap_allocation mode object amount).
Proof.
  intros before world after next[SIDE[PRIVATE[ORIGIN BLOCK]]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
    as[NEXT[[RETAIN_NATIVE RETAIN_STABLE]FRAME]].
  destruct BLOCK as[BOUND[HEADER OWNED]].
  assert(LIVE:Mem.valid_block before object)by(eapply Mem.perm_valid_block;apply(OWNED(-8));lia).
  assert(REGION:Mem.unchanged_on(gateway_heap_region object amount)before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros candidate position[SAME RANGE]VALID;subst candidate;split;
      [left;exact PRIVATE|unfold gateway_native_no_output;tauto]. }
  split;[exact NEXT|]. split;[apply RETAIN_NATIVE;assumption|]. split;[exact ORIGIN|].
  exact(gateway_heap_block_frame before after object amount(conj BOUND(conj HEADER OWNED))REGION).
Qed.
