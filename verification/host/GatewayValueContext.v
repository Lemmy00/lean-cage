(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Parser-owned stream and stack cells survive actual ambient steps. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
Require Import ReceiverAllocation.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayStreamMemory
  GatewayValueEntry GatewayValueNodeMemory GatewayFrames GatewayWordsMemory GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Section ValueContext.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).

Definition gateway_value_context stream_block stream_offset initial readonly original memory world :Prop:=
  discipline None memory world /\native world stream_block /\
  (forall object position,readonly object position->stable world object position) /\
  gateway_value_inputs memory stream_block stream_offset initial readonly /\Mem.unchanged_on readonly original memory.

Lemma gateway_value_context_ambient stream_block stream_offset initial readonly original :
  gateway_ambient_closed backend(gateway_value_context stream_block stream_offset initial readonly original).
Proof.
  intros before world after next[SIDE[STREAM[READONLY[INPUT INITIAL_FRAME]]]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)
    as[NEXT_SIDE[[RETAIN_NATIVE RETAIN_STABLE]STEP_FRAME]].
  assert(FRAME:Mem.unchanged_on(gateway_value_input_region stream_block stream_offset readonly)before after).
  { eapply gateway_native_frame_restrict;[exact STEP_FRAME| |intros;unfold gateway_native_no_output;tauto].
    intros object position[REGION|READ];[destruct REGION as[SAME RANGE];subst object;left;exact STREAM|
      right;apply READONLY;exact READ]. }
  split;[exact NEXT_SIDE|]. split.
  - apply RETAIN_NATIVE;[|exact STREAM]. eapply Mem.perm_valid_block.
    apply(gateway_value_stream_owned _ _ _ _ _ INPUT(Ptrofs.unsigned stream_offset));lia.
  - split.
    + intros object position READ;apply RETAIN_STABLE.
      * apply(gateway_value_readonly_readable _ _ _ _ _ INPUT);exact READ.
      * apply READONLY;exact READ.
    + split;[eapply gateway_value_inputs_frame;eassumption|].
      eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|].
      eapply Mem.unchanged_on_implies;[exact FRAME|intros;right;assumption].
Qed.

Definition gateway_value_allocated slots stream_block stream_offset initial readonly original memory world :Prop:=
  gateway_value_context stream_block stream_offset initial readonly original memory world /\
  native world(gateway_value_tag_slot slots) /\native world(gateway_value_size_slot slots) /\
  Mem.range_perm memory(gateway_value_tag_slot slots)0 8 Cur Freeable /\
  Mem.range_perm memory(gateway_value_size_slot slots)0 8 Cur Freeable /\
  gateway_value_tag_slot slots<>gateway_value_size_slot slots /\
  gateway_value_tag_slot slots<>stream_block /\gateway_value_size_slot slots<>stream_block /\
  (forall position,~readonly(gateway_value_tag_slot slots)position) /\
  (forall position,~readonly(gateway_value_size_slot slots)position).

Lemma gateway_value_context_allocated before world after slots stream_block stream_offset initial readonly original :
  gateway_value_context stream_block stream_offset initial readonly original before world ->
  gateway_value_allocations before slots after ->
  gateway_value_allocated slots stream_block stream_offset initial readonly original after world.
Proof.
  intros[SIDE[STREAM[READONLY[INPUT INITIAL_FRAME]]]]ALLOC.
  destruct(gateway_value_slots_separate _ _ _ _ _ _ _ INPUT ALLOC)
    as[AFTER_INPUT[TAG_STREAM[SIZE_STREAM[TAG_READONLY SIZE_READONLY]]]].
  pose proof(gateway_value_allocation_chain _ _ _ ALLOC)as CHAIN.
  pose proof(local_allocations_objects _ _ _ CHAIN)as OBJECTS.
  inversion OBJECTS as[|? ? TAG TAIL];subst;inversion TAIL as[|? ? SIZE REST];subst.
  pose proof(local_allocations_distinct _ _ _ CHAIN)as DISTINCT.
  inversion DISTINCT as[|? ? NOTIN NO_DUP];subst.
  pose proof ALLOC as[middle[TAG_ALLOC SIZE_ALLOC]].
  assert(MIDDLE_SIDE:discipline None middle world).
  { eapply gateway_thread_native_alloc;[exact runtime|exact SIDE|exact TAG_ALLOC]. }
  split.
  - split;[eapply gateway_thread_native_alloc;[exact runtime|exact MIDDLE_SIDE|exact SIZE_ALLOC]|].
    split;[exact STREAM|]. split;[exact READONLY|]. split;[exact AFTER_INPUT|].
    eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|eapply local_allocations_unchanged;exact CHAIN].
  - split;[eapply gateway_thread_fresh_native;[exact runtime|exact SIDE|exact(proj1 TAG)]|].
    split;[eapply gateway_thread_fresh_native;[exact runtime|exact SIDE|exact(proj1 SIZE)]|].
    split;[exact(proj2 TAG)|]. split;[exact(proj2 SIZE)|].
    split;[intro SAME;apply NOTIN;cbn;auto|]. split;[exact TAG_STREAM|]. split;[exact SIZE_STREAM|].
    split;assumption.
Qed.

Lemma gateway_value_allocated_ambient slots stream_block stream_offset initial readonly original :
  gateway_ambient_closed backend(gateway_value_allocated slots stream_block stream_offset initial readonly original).
Proof.
  intros before world after next[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]]INTERFERENCE.
  pose proof(gateway_value_context_ambient _ _ _ _ _ _ _ _ _ CONTEXT INTERFERENCE)as AFTER_CONTEXT.
  destruct CONTEXT as[SIDE REST_CONTEXT].
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)
    as[AFTER_SIDE[[RETAIN_NATIVE RETAIN_STABLE]FRAME]].
  split;[exact AFTER_CONTEXT|].
  split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia|exact TAG]|].
  split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(SIZE_OWN 0);lia|exact SIZE]|].
  split.
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply TAG_OWN;exact RANGE].
    split;[left;exact TAG|unfold gateway_native_no_output;tauto].
  - split;[|exact REST]. intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply SIZE_OWN;exact RANGE].
    split;[left;exact SIZE|unfold gateway_native_no_output;tauto].
Qed.

Lemma gateway_value_allocated_node_store slots stream_block stream_offset initial readonly original before world after :
  gateway_value_allocated slots stream_block stream_offset initial readonly original before world ->
  Mem.store Mint64 before stream_block(Ptrofs.unsigned stream_offset+32)
    (Vlong(Int64.sub(stream_nodes initial)Int64.one))=Some after ->
  gateway_value_allocated slots stream_block stream_offset(gateway_stream_node_debit initial)readonly original after world.
Proof.
  intros[[SIDE[STREAM[READONLY[INPUT INITIAL_FRAME]]]][TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]]STORE.
  destruct(gateway_value_node_inputs _ _ _ _ _ _ INPUT STORE)as[AFTER_INPUT FRAME].
  split.
  - split;[eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact STREAM|exact STORE]|].
    split;[exact STREAM|]. split;[exact READONLY|]. split;[exact AFTER_INPUT|].
    eapply Mem.unchanged_on_trans;eassumption.
  - split;[exact TAG|]. split;[exact SIZE|].
    split;[intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply TAG_OWN;exact RANGE]|].
    split;[intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply SIZE_OWN;exact RANGE]|exact REST].
Qed.

End ValueContext.
