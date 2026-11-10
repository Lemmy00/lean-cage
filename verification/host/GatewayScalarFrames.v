(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Individual native effects preserve the same initialized scalar cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueRegions
  GatewayScalarLength GatewayScalarContext GatewayStreamInterface GatewayThreadRuntime GatewayWordsMemory.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_value_context_effect {World}native stable discipline stream_block stream_offset initial readonly original
    before world after next :
  @gateway_value_context World native stable discipline stream_block stream_offset initial readonly original before world ->
  discipline None after next ->gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original after next.
Proof.
  intros[SIDE[STREAM[READONLY[INPUT INITIAL_FRAME]]]]NEXT_SIDE[RETAIN_NATIVE RETAIN_STABLE]STEP_FRAME.
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

Lemma gateway_value_active_effect {World}native stable discipline slots stream_block stream_offset initial readonly original
    before world after next :
  @gateway_value_active World native stable discipline slots stream_block stream_offset initial readonly original before world ->
  discipline None after next ->gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_value_active native stable discipline slots stream_block stream_offset initial readonly original after next.
Proof.
  intros[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]]SIDE[RETAIN_NATIVE RETAIN_STABLE]FRAME;split.
  - eapply gateway_value_context_effect;[exact CONTEXT|exact SIDE|split;assumption|exact FRAME].
  - split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia|exact TAG]|].
    split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(SIZE_OWN 0);lia|exact SIZE]|].
    split.
    + intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply TAG_OWN;exact RANGE].
      split;[left;exact TAG|unfold gateway_native_no_output;tauto].
    + split;[|exact REST]. intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply SIZE_OWN;exact RANGE].
      split;[left;exact SIZE|unfold gateway_native_no_output;tauto].
Qed.

Theorem gateway_value_sized_effect {World}native stable discipline scalar slots stream_block stream_offset initial readonly original size
    before world after next :
  @gateway_value_sized World native stable discipline scalar slots stream_block stream_offset initial readonly original size before world ->
  discipline None after next ->gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size after next.
Proof.
  intros[[ACTIVE TAG_LOAD]SIZE_LOAD]SIDE RETAINED FRAME.
  pose proof ACTIVE as[CONTEXT[TAG[SIZE REST]]].
  split.
  - split;[eapply gateway_value_active_effect;eassumption|].
    change(Mem.load Mint64 before(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_scalar_code scalar))))in TAG_LOAD.
    change(Mem.load Mint64 after(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_scalar_code scalar)))).
    eapply Mem.load_unchanged_on;[exact FRAME| |exact TAG_LOAD].
    intros position RANGE;split;[left;exact TAG|unfold gateway_native_no_output;tauto].
  - change(Mem.load Mint64 before(gateway_value_size_slot slots)0=Some(Vlong size))in SIZE_LOAD.
    change(Mem.load Mint64 after(gateway_value_size_slot slots)0=Some(Vlong size)).
    eapply Mem.load_unchanged_on;[exact FRAME| |exact SIZE_LOAD].
    intros position RANGE;split;[left;exact SIZE|unfold gateway_native_no_output;tauto].
Qed.
