(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The value caller keeps its other real word cell while reading a tag. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayValueEntry GatewayValueContext GatewayStreamInterface
  GatewayStreamMemory GatewayWordContext GatewayWordInputs GatewayWordsMemory GatewayThreadRuntime GatewayNativeRoots.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_value_active {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)slots stream_block stream_offset initial readonly original memory world :Prop:=
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original memory world /\
  native world(gateway_value_tag_slot slots) /\native world(gateway_value_size_slot slots) /\
  Mem.range_perm memory(gateway_value_tag_slot slots)0 8 Cur Writable /\
  Mem.range_perm memory(gateway_value_size_slot slots)0 8 Cur Writable /\
  gateway_value_tag_slot slots<>gateway_value_size_slot slots /\
  gateway_value_tag_slot slots<>stream_block /\gateway_value_size_slot slots<>stream_block /\
  (forall position,~readonly(gateway_value_tag_slot slots)position) /\
  (forall position,~readonly(gateway_value_size_slot slots)position).

Theorem gateway_value_allocated_active {World}native stable discipline slots stream_block stream_offset
    initial readonly original memory world :
  @gateway_value_allocated World native stable discipline slots stream_block stream_offset initial readonly original memory world ->
  gateway_value_active native stable discipline slots stream_block stream_offset initial readonly original memory world.
Proof.
  intros[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]].
  split;[exact CONTEXT|]. split;[exact TAG|]. split;[exact SIZE|].
  split;[intros position RANGE;eapply Mem.perm_implies;[apply TAG_OWN;exact RANGE|constructor]|].
  split;[intros position RANGE;eapply Mem.perm_implies;[apply SIZE_OWN;exact RANGE|constructor]|exact REST].
Qed.

Definition gateway_value_keep_size slots readonly object position :Prop:=
  readonly object position \/gateway_byte_region(gateway_value_size_slot slots)0 8 object position.

Section ValueStack.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).

Theorem gateway_value_active_tag_context slots stream_block stream_offset initial readonly original before world :
  gateway_value_active native stable discipline slots stream_block stream_offset initial readonly original before world ->
  gateway_word_context native stable
    (fun mode memory world=>discipline mode memory world /\
      gateway_native_roots native[gateway_value_size_slot slots]memory world)
    stream_block stream_offset initial(gateway_value_tag_slot slots)Ptrofs.zero
    (gateway_value_keep_size slots readonly)before before world.
Proof.
  intros[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN[DIFFERENT[TAG_STREAM[SIZE_STREAM[TAG_READ SIZE_READ]]]]]]]]].
  destruct CONTEXT as[SIDE[STREAM[READONLY[INPUT FRAME]]]].
  assert(SIZE_LIVE:Mem.valid_block before(gateway_value_size_slot slots)).
  { eapply Mem.perm_valid_block;apply(SIZE_OWN 0);lia. }
  split.
  - split;[exact SIDE|]. intros object[MEMBER|MEMBER];[subst object;split;assumption|contradiction].
  - split;[exact STREAM|]. split;[exact TAG|]. split.
    + intros object position[READ|[SAME RANGE]].
      * apply READONLY;exact READ.
      * subst object;eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact SIZE].
    + split;[|apply Mem.unchanged_on_refl]. split;[|change(8|0);exists 0;reflexivity].
      constructor.
      * exact(gateway_value_stream_cells _ _ _ _ _ INPUT).
      * change(0<=8<=18446744073709551615);lia.
      * exact(gateway_value_stream_bounds _ _ _ _ _ INPUT).
      * change(8<=18446744073709551616);lia.
      * exact(gateway_value_stream_owned _ _ _ _ _ INPUT).
      * eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia.
      * exact TAG_OWN.
      * left;congruence.
      * intros object position[READ|[SAME RANGE]].
        -- eapply gateway_value_readonly_live;[exact INPUT|exact READ].
        -- subst object;exact SIZE_LIVE.
      * intros object position[READ|[SAME RANGE]].
        -- eapply gateway_value_readonly_readable;[exact INPUT|exact READ].
        -- subst object;eapply Mem.perm_implies;[apply SIZE_OWN;exact RANGE|constructor].
      * intros position RANGE[READ|[SAME SIZE_RANGE]];[exact(TAG_READ position READ)|congruence].
      * intros position RANGE[READ|[SAME SIZE_RANGE]].
        -- eapply(gateway_value_readonly_counters _ _ _ _ _ INPUT position);[lia|exact READ].
        -- congruence.
      * intros position RANGE[READ|[SAME SIZE_RANGE]].
        -- eapply(gateway_value_readonly_cancel _ _ _ _ _ INPUT position);[exact RANGE|exact READ].
        -- congruence.
Qed.

Theorem gateway_value_tag_context_active slots stream_block stream_offset initial final_stream readonly original
    before world after next :
  gateway_value_active native stable discipline slots stream_block stream_offset initial readonly original before world ->
  gateway_word_context native stable
    (fun mode memory world=>discipline mode memory world /\
      gateway_native_roots native[gateway_value_size_slot slots]memory world)
    stream_block stream_offset final_stream(gateway_value_tag_slot slots)Ptrofs.zero
    (gateway_value_keep_size slots readonly)before after next ->
  gateway_value_active native stable discipline slots stream_block stream_offset final_stream readonly original after next.
Proof.
  intros[OLD_CONTEXT[OLD_TAG[OLD_SIZE[OLD_TAG_OWN[OLD_SIZE_OWN REST]]]]]
    [[SIDE HELD][STREAM[TAG[READONLY[[RAW ALIGNMENT]FRAME]]]]].
  pose proof OLD_CONTEXT as[OLD_SIDE[OLD_STREAM[OLD_READONLY[OLD_INPUT OLD_FRAME]]]].
  split.
  - split;[exact SIDE|]. split;[exact STREAM|]. split.
    + intros object position READ;apply READONLY;left;exact READ.
    + split;[|eapply Mem.unchanged_on_trans;[exact OLD_FRAME|]].
      * constructor.
        -- exact(gateway_read_stream_cells _ _ _ _ _ _ _ _ RAW).
        -- exact(gateway_read_stream_bounds _ _ _ _ _ _ _ _ RAW).
        -- exact(gateway_read_stream_owned _ _ _ _ _ _ _ _ RAW).
        -- intros object position READ;eapply gateway_read_readonly_live;[exact RAW|left;exact READ].
        -- intros object position READ;eapply gateway_read_readonly_readable;[exact RAW|left;exact READ].
        -- exact(gateway_value_readonly_cancel _ _ _ _ _ OLD_INPUT).
        -- exact(gateway_value_readonly_counters _ _ _ _ _ OLD_INPUT).
      * eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption].
  - split;[exact TAG|].
    split;[exact(proj2(HELD(gateway_value_size_slot slots)ltac:(left;reflexivity)))|].
    split;[exact(gateway_read_data_owned _ _ _ _ _ _ _ _ RAW)|].
    split;[|exact REST].
    intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply OLD_SIZE_OWN;exact RANGE].
    right;split;[reflexivity|exact RANGE].
Qed.

End ValueStack.
