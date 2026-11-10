(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Word output ownership is raw geometry, independent of stream success. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayStreamInterface GatewayStreamMemory GatewayFrames GatewayWordsMemory.
Open Scope Z_scope.

(* Reuse the raw stream/region geometry for an eight-byte caller output cell.
   This does not assert that eight bytes remain in the input stream. *)
Definition gateway_word_inputs before stream_block stream_offset stream output output_offset readonly :Prop:=
  gateway_read_inputs before stream_block stream_offset stream output output_offset 8 readonly /\
    (8|Ptrofs.unsigned output_offset).

Lemma gateway_loadv_all_frame before after chunk pointer value :
  Mem.unchanged_on(fun _ _=>True)before after ->Mem.loadv chunk before pointer=Some value ->
  Mem.loadv chunk after pointer=Some value.
Proof.
  intros FRAME LOAD;destruct pointer;cbn[Mem.loadv]in *;try discriminate.
  destruct(zle _ _);[|discriminate].
  eapply Mem.load_unchanged_on;[exact FRAME|intros;exact I|exact LOAD].
Qed.

Lemma gateway_stream_all_frame before after block offset stream :
  Mem.unchanged_on(fun _ _=>True)before after ->
  gateway_stream_memory before block offset stream ->gateway_stream_memory after block offset stream.
Proof.
  intros FRAME STREAM;unfold gateway_stream_memory in *.
  repeat match goal with H:_ /\_|-_=>destruct H end.
  repeat split;eapply gateway_loadv_all_frame;eassumption.
Qed.

Lemma gateway_read_inputs_all_frame before after stream_block stream_offset stream output output_offset amount readonly :
  Mem.unchanged_on(fun _ _=>True)before after ->
  gateway_read_inputs before stream_block stream_offset stream output output_offset amount readonly ->
  gateway_read_inputs after stream_block stream_offset stream output output_offset amount readonly.
Proof.
  intros FRAME INPUT;destruct INPUT as[CELLS AMOUNT STREAM_BOUNDS DATA_BOUNDS
    STREAM_OWNED DATA_LIVE DATA_OWNED SEPARATE READONLY_LIVE READONLY_READABLE
    READONLY_DATA READONLY_REMAINING READONLY_CANCEL];constructor;try assumption.
  - eapply gateway_stream_all_frame;eassumption.
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|exact I|].
    apply STREAM_OWNED;exact RANGE.
  - eapply Mem.valid_block_unchanged_on;eassumption.
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|exact I|].
    apply DATA_OWNED;exact RANGE.
  - intros block position READ;eapply Mem.valid_block_unchanged_on;[exact FRAME|].
    apply READONLY_LIVE with(position:=position);exact READ.
  - intros block position READ;eapply Mem.perm_unchanged_on;[exact FRAME|exact I|].
    apply READONLY_READABLE;exact READ.
Qed.

Definition gateway_read_input_region stream_block stream_offset output output_offset amount readonly
    object position :Prop:=
  gateway_stream_region stream_block stream_offset object position \/
  gateway_byte_region output(Ptrofs.unsigned output_offset)(Z.to_nat amount)object position \/
  readonly object position.

Lemma gateway_read_inputs_region_frame before after stream_block stream_offset stream output output_offset amount readonly :
  Mem.unchanged_on(gateway_read_input_region stream_block stream_offset output output_offset amount readonly)before after ->
  gateway_read_inputs before stream_block stream_offset stream output output_offset amount readonly ->
  gateway_read_inputs after stream_block stream_offset stream output output_offset amount readonly.
Proof.
  intros FRAME INPUT;destruct INPUT as[CELLS AMOUNT STREAM_BOUNDS DATA_BOUNDS
    STREAM_OWNED DATA_LIVE DATA_OWNED SEPARATE READONLY_LIVE READONLY_READABLE
    READONLY_DATA READONLY_REMAINING READONLY_CANCEL];constructor;try assumption.
  - eapply gateway_stream_memory_closed;[exact STREAM_BOUNDS|exact CELLS|].
    eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption].
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply STREAM_OWNED;exact RANGE].
    left;split;[reflexivity|exact RANGE].
  - eapply Mem.valid_block_unchanged_on;eassumption.
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply DATA_OWNED;exact RANGE].
    right;left;split;[reflexivity|]. unfold gateway_byte_region;rewrite Z2Nat.id by lia;exact RANGE.
  - intros block position READ;eapply Mem.valid_block_unchanged_on;[exact FRAME|].
    apply READONLY_LIVE with(position:=position);exact READ.
  - intros block position READ;eapply Mem.perm_unchanged_on;[exact FRAME|right;right;exact READ|].
    apply READONLY_READABLE;exact READ.
Qed.

Theorem gateway_word_input_output_access before stream_block stream_offset stream output output_offset readonly :
  gateway_word_inputs before stream_block stream_offset stream output output_offset readonly ->
  Mem.valid_access before Mint64 output(Ptrofs.unsigned output_offset)Writable /\
    Ptrofs.unsigned output_offset+8<=Ptrofs.modulus.
Proof.
  intros[RAW ALIGNED];split.
  - split;[exact(gateway_read_data_owned _ _ _ _ _ _ _ _ RAW)|exact ALIGNED].
  - exact(gateway_read_data_bounds _ _ _ _ _ _ _ _ RAW).
Qed.

Theorem gateway_actual_word_scratch_geometry before allocated buffer stream_block stream_offset stream
    output output_offset readonly :
  gateway_word_inputs before stream_block stream_offset stream output output_offset readonly ->
  Mem.alloc before 0 8=(allocated,buffer) ->
  gateway_word_inputs allocated stream_block stream_offset stream output output_offset readonly /\
  Mem.range_perm allocated buffer 0 8 Cur Freeable /\buffer<>stream_block /\buffer<>output /\
    (forall position,~readonly buffer position).
Proof.
  intros[RAW ALIGNED]ALLOC.
  assert(FRAME:Mem.unchanged_on(fun _ _=>True)before allocated)by(eapply Mem.alloc_unchanged_on;exact ALLOC).
  assert(FRESH:~Mem.valid_block before buffer)by(eapply Mem.fresh_block_alloc;exact ALLOC).
  assert(STREAM:Mem.valid_block before stream_block).
  { eapply Mem.perm_valid_block.
    apply(gateway_read_stream_owned _ _ _ _ _ _ _ _ RAW(Ptrofs.unsigned stream_offset));lia. }
  split;[split;[eapply gateway_read_inputs_all_frame;eassumption|exact ALIGNED]|].
  split;[intros position RANGE;eapply Mem.perm_alloc_2;eauto|].
  split;[intro SAME;subst buffer;exact(FRESH STREAM)|].
  split.
  - intro SAME;subst buffer;apply FRESH;exact(gateway_read_data_live _ _ _ _ _ _ _ _ RAW).
  - intros position READ;apply FRESH;exact(gateway_read_readonly_live _ _ _ _ _ _ _ _ RAW buffer position READ).
Qed.

Definition gateway_word_scratch_readonly(buffer:block)width(output:block)output_offset readonly object position :Prop:=
  readonly object position \/
  (object=output /\Ptrofs.unsigned output_offset<=position<Ptrofs.unsigned output_offset+8) \/
  (object=buffer /\width<=position<8).

Theorem gateway_word_scratch_read_inputs memory buffer stream_block stream_offset stream
    output output_offset readonly width :
  gateway_word_inputs memory stream_block stream_offset stream output output_offset readonly ->
  Mem.range_perm memory buffer 0 8 Cur Freeable ->buffer<>stream_block ->buffer<>output ->
  (forall position,~readonly buffer position) ->0<=width<=8 ->
  gateway_read_inputs memory stream_block stream_offset stream buffer Ptrofs.zero width
    (gateway_word_scratch_readonly buffer width output output_offset readonly).
Proof.
  intros[RAW ALIGNED]FREEABLE STREAM_SEPARATE OUTPUT_SEPARATE NO_READONLY WIDTH;constructor.
  - exact(gateway_read_stream_cells _ _ _ _ _ _ _ _ RAW).
  - change(0<=width<=18446744073709551615);lia.
  - exact(gateway_read_stream_bounds _ _ _ _ _ _ _ _ RAW).
  - change(0+width<=18446744073709551616);lia.
  - exact(gateway_read_stream_owned _ _ _ _ _ _ _ _ RAW).
  - eapply Mem.perm_valid_block with(ofs:=0)(k:=Cur)(p:=Freeable);apply FREEABLE;lia.
  - intros position RANGE;eapply Mem.perm_implies;[apply FREEABLE;change(0<=position<width)in RANGE;lia|constructor].
  - left;congruence.
  - intros object position[READ|[[SAME RANGE]|[SAME RANGE]]].
    + exact(gateway_read_readonly_live _ _ _ _ _ _ _ _ RAW object position READ).
    + subst object;exact(gateway_read_data_live _ _ _ _ _ _ _ _ RAW).
    + subst object;eapply Mem.perm_valid_block with(ofs:=0)(k:=Cur)(p:=Freeable);apply FREEABLE;lia.
  - intros object position[READ|[[SAME RANGE]|[SAME RANGE]]].
    + exact(gateway_read_readonly_readable _ _ _ _ _ _ _ _ RAW object position READ).
    + subst object;eapply Mem.perm_implies;[apply(gateway_read_data_owned _ _ _ _ _ _ _ _ RAW);exact RANGE|constructor].
    + subst object;eapply Mem.perm_implies;[apply FREEABLE;lia|constructor].
  - intros position RANGE[READ|[[SAME OUT]|[SAME TAIL]]].
    + exact(NO_READONLY position READ).
    + contradiction.
    + change(0<=position<width)in RANGE;lia.
  - intros position RANGE[READ|[[SAME OUT]|[SAME TAIL]]].
    + exact(gateway_read_readonly_remaining _ _ _ _ _ _ _ _ RAW position RANGE READ).
    + subst stream_block.
      destruct(gateway_read_data_separate _ _ _ _ _ _ _ _ RAW)as[DIFFERENT|[BEFORE|AFTER]];[congruence|lia|lia].
    + congruence.
  - intros position RANGE[READ|[[SAME OUT]|[SAME TAIL]]].
    + exact(gateway_read_readonly_cancel _ _ _ _ _ _ _ _ RAW position RANGE READ).
    + subst stream_block.
      destruct(gateway_read_data_separate _ _ _ _ _ _ _ _ RAW)as[DIFFERENT|[BEFORE|AFTER]];[congruence|lia|lia].
    + congruence.
Qed.
