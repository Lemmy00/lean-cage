(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A real read preserves unused scratch and caller output cells. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewayStreamMemory GatewayThreadRuntime
  GatewayWordInputs GatewayWordContext GatewayWordRuntime GatewayStreamWord GatewayFrames GatewayWordsMemory
  GatewayReadonlyRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_word_post_readonly stream_block stream_offset readonly object position :Prop:=
  gateway_stream_region stream_block stream_offset object position \/readonly object position.

Section WordReadReceipt.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option Values.val->Memory.mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

Theorem gateway_word_after_read_ready buffer stream_block stream_offset stream output output_offset readonly original
    before world width reading after next bytes :
  gateway_word_scratch_context native_private stable_readonly discipline buffer stream_block stream_offset stream
    output output_offset readonly original before world ->0<=width<=8 ->
  gateway_read_receipt io before stream_block stream_offset stream buffer Ptrofs.zero width
    (gateway_word_scratch_readonly buffer width output output_offset readonly)reading after bytes ->
  discipline None after next ->native_private next stream_block ->native_private next buffer ->
  (forall object position,gateway_word_scratch_readonly buffer width output output_offset readonly object position ->
    stable_readonly next object position) ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_word_stage native_private stable_readonly discipline None buffer output[stream_block]
    (gateway_word_post_readonly stream_block stream_offset readonly)after
    (gateway_word_store_ready buffer output(Ptrofs.unsigned output_offset))after next.
Proof.
  intros[CALL_SIDE[BUFFER[FREEABLE[SEPARATE[OUTSIDE AVOIDS]]]]]WIDTH RECEIPT
    SIDE_AFTER STREAM_AFTER BUFFER_AFTER STABLE_AFTER[RETAIN_NATIVE RETAIN_STABLE].
  destruct CALL_SIDE as[SIDE[STREAM[OUTPUT[READONLY[[RAW ALIGNED]INITIAL_FRAME]]]]].
  destruct RECEIPT as[COUNT FITS OBSERVED INITIALIZED DATA_PERMS STREAM_PERMS FINAL_STREAM FRAME].
  assert(OUTPUT_AFTER:native_private next output).
  { apply RETAIN_NATIVE;[exact(gateway_read_data_live _ _ _ _ _ _ _ _ RAW)|exact OUTPUT]. }
  assert(READ_FRAME:Mem.unchanged_on readonly before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption]. }
  assert(OUTPUT_FRAME:Mem.unchanged_on(gateway_byte_region output(Ptrofs.unsigned output_offset)8)before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|]. intros object position REGION;right;left;exact REGION. }
  split.
  - split;[exact SIDE_AFTER|]. split;[exact BUFFER_AFTER|]. split;[exact OUTPUT_AFTER|].
    split.
    + eapply Mem.valid_block_unchanged_on;[exact FRAME|].
      eapply Mem.perm_valid_block with(ofs:=0)(k:=Cur)(p:=Freeable);apply FREEABLE;lia.
    + split;[eapply Mem.valid_block_unchanged_on;[exact FRAME|exact(gateway_read_data_live _ _ _ _ _ _ _ _ RAW)]|].
      split.
      * intros object[MEMBER|MEMBER];[subst object|contradiction]. split;[|exact STREAM_AFTER].
        eapply Mem.valid_block_unchanged_on;[exact FRAME|]. eapply Mem.perm_valid_block.
        apply(gateway_read_stream_owned _ _ _ _ _ _ _ _ RAW(Ptrofs.unsigned stream_offset));lia.
      * split;[|apply Mem.unchanged_on_refl].
        intros object position[REGION|READ].
        -- destruct REGION as[SAME RANGE];subst object;split.
           ++ apply(proj1(STREAM_PERMS position Cur Readable RANGE)).
              eapply Mem.perm_implies;[apply(gateway_read_stream_owned _ _ _ _ _ _ _ _ RAW);exact RANGE|constructor].
           ++ left;exact STREAM_AFTER.
        -- split.
           ++ eapply Mem.perm_unchanged_on;[exact READ_FRAME|exact READ|].
              apply(gateway_read_readonly_readable _ _ _ _ _ _ _ _ RAW);exact READ.
           ++ right;apply STABLE_AFTER;left;exact READ.
  - split.
    + intros position RANGE;destruct(Z_lt_ge_dec position width)as[PREFIX|TAIL].
      * apply(proj1(DATA_PERMS position Cur Freeable ltac:(change(0<=position<width);lia))).
        apply FREEABLE;exact RANGE.
      * eapply Mem.perm_unchanged_on;[exact FRAME| |apply FREEABLE;exact RANGE].
        right;right;split;[reflexivity|lia].
    + split;[|exact ALIGNED]. intros position RANGE.
      eapply Mem.perm_unchanged_on;[exact OUTPUT_FRAME|split;[reflexivity|exact RANGE]|].
      apply(gateway_read_data_owned _ _ _ _ _ _ _ _ RAW);exact RANGE.
Qed.

Lemma gateway_word_post_readonly_output stream_block stream_offset output output_offset readonly memory stream :
  gateway_word_inputs memory stream_block stream_offset stream output output_offset readonly ->
  forall position,Ptrofs.unsigned output_offset<=position<Ptrofs.unsigned output_offset+8 ->
    ~gateway_word_post_readonly stream_block stream_offset readonly output position.
Proof.
  intros[RAW ALIGNED]position RANGE[[SAME STREAM_RANGE]|READ].
  - subst output;destruct(gateway_read_data_separate _ _ _ _ _ _ _ _ RAW)
      as[DIFFERENT|[BEFORE|AFTER]];[congruence|lia|lia].
  - exact(gateway_read_readonly_data _ _ _ _ _ _ _ _ RAW position RANGE READ).
Qed.

Lemma gateway_word_post_readonly_scratch buffer stream_block stream_offset readonly :
  buffer<>stream_block ->(forall position,~readonly buffer position) ->
  forall position,~gateway_word_post_readonly stream_block stream_offset readonly buffer position.
Proof. intros DIFFERENT AVOIDS position[[SAME RANGE]|READ];[congruence|exact(AVOIDS position READ)]. Qed.

Lemma gateway_word_stage_get_contract stream_block stream_offset readonly original buffer output output_offset count :
  gateway_coupled_private_contract backend(gateway_byte_region buffer 0 count)
    (gateway_word_stage native_private stable_readonly discipline None buffer output[stream_block]
      (gateway_word_post_readonly stream_block stream_offset readonly)original
      (gateway_word_store_ready buffer output(Ptrofs.unsigned output_offset))).
Proof.
  constructor;intros before world after next STAGE INTERFERENCE;split.
  - eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned output_offset);
      [exact runtime| |exact STAGE|exact INTERFERENCE].
    eapply gateway_word_stage_region_closed;apply gateway_word_store_ready_closed.
  - destruct STAGE as[[SIDE[BUFFER REST]]READY].
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)
      as[_[_ FRAME]].
    eapply gateway_native_frame_restrict;[exact FRAME| |intros;unfold gateway_native_no_output;tauto].
    intros object position[SAME RANGE];subst object;left;exact BUFFER.
Qed.

End WordReadReceipt.
