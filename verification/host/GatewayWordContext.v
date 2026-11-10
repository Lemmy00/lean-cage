(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual word inputs retain their private runtime ownership. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewayStreamMemory GatewayWordInputs GatewayFrames GatewayWordsMemory GatewayOperations.
Open Scope Z_scope.

Section WordContext.
Context {World Event}(backend:gateway_backend World Event)
  (io:Event->option gateway_native_io)(native_private:World->block->Prop)
  (stable_readonly:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
  (thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

Definition gateway_word_context stream_block stream_offset stream output output_offset readonly original memory world :Prop:=
  discipline None memory world /\native_private world stream_block /\native_private world output /\
  (forall object position,readonly object position->stable_readonly world object position) /\
  gateway_word_inputs memory stream_block stream_offset stream output output_offset readonly /\
  Mem.unchanged_on readonly original memory.

Definition gateway_word_scratch_context buffer stream_block stream_offset stream output output_offset readonly
    original memory world :Prop:=
  gateway_word_context stream_block stream_offset stream output output_offset readonly original memory world /\
  native_private world buffer /\Mem.range_perm memory buffer 0 8 Cur Freeable /\
  buffer<>stream_block /\buffer<>output /\(forall position,~readonly buffer position).

Lemma gateway_word_context_ambient stream_block stream_offset stream output output_offset readonly original :
  gateway_runtime_discipline backend
    (gateway_word_context stream_block stream_offset stream output output_offset readonly original).
Proof.
  intros before world after next[SIDE[STREAM[OUTPUT[READONLY[INPUT INITIAL_FRAME]]]]]INTERFERENCE.
  destruct INPUT as[RAW ALIGNMENT].
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)
    as[NEXT_SIDE[[RETAIN_NATIVE RETAIN_STABLE]STEP_FRAME]].
  assert(FRAME:Mem.unchanged_on
    (gateway_read_input_region stream_block stream_offset output output_offset 8 readonly)before after).
  { eapply gateway_native_frame_restrict;[exact STEP_FRAME| |intros;unfold gateway_native_no_output;tauto].
    intros object position[REGION|[REGION|READ]].
    - destruct REGION as[SAME RANGE];subst object;left;exact STREAM.
    - destruct REGION as[SAME RANGE];subst object;left;exact OUTPUT.
    - right;apply READONLY;exact READ. }
  split;[exact NEXT_SIDE|].
  split.
  - apply RETAIN_NATIVE;[|exact STREAM]. eapply Mem.perm_valid_block.
    apply(gateway_read_stream_owned _ _ _ _ _ _ _ _ RAW(Ptrofs.unsigned stream_offset));lia.
  - split;[apply RETAIN_NATIVE;[exact(gateway_read_data_live _ _ _ _ _ _ _ _ RAW)|exact OUTPUT]|].
    split.
    + intros object position READ;apply RETAIN_STABLE.
      * apply(gateway_read_readonly_readable _ _ _ _ _ _ _ _ RAW);exact READ.
      * apply READONLY;exact READ.
    + split.
      * split;[eapply gateway_read_inputs_region_frame;eassumption|exact ALIGNMENT].
      * eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|].
        eapply Mem.unchanged_on_implies;[exact FRAME|intros;right;right;assumption].
Qed.

Lemma gateway_word_context_alloc before world after buffer stream_block stream_offset stream
    output output_offset readonly original :
  gateway_word_context stream_block stream_offset stream output output_offset readonly original before world ->
  Mem.alloc before 0 8=(after,buffer) ->
  gateway_word_scratch_context buffer stream_block stream_offset stream output output_offset readonly original after world.
Proof.
  intros[SIDE[STREAM[OUTPUT[READONLY[INPUT INITIAL_FRAME]]]]]ALLOC.
  destruct(gateway_actual_word_scratch_geometry before after buffer stream_block stream_offset stream
    output output_offset readonly INPUT ALLOC)as[AFTER[FREEABLE[SEPARATE[OUTSIDE AVOIDS]]]].
  split.
  - split;[eapply gateway_thread_native_alloc;[exact runtime|exact SIDE|exact ALLOC]|].
    split;[exact STREAM|]. split;[exact OUTPUT|]. split;[exact READONLY|]. split;[exact AFTER|].
    eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|]. eapply Mem.alloc_unchanged_on;exact ALLOC.
  - split.
    + eapply gateway_thread_fresh_native;[exact runtime|exact SIDE|].
      eapply Mem.fresh_block_alloc;exact ALLOC.
    + split;[exact FREEABLE|]. split;[exact SEPARATE|]. split;assumption.
Qed.

Lemma gateway_word_scratch_context_ambient buffer stream_block stream_offset stream output output_offset readonly original :
  gateway_runtime_discipline backend
    (gateway_word_scratch_context buffer stream_block stream_offset stream output output_offset readonly original).
Proof.
  intros before world after next[INPUT[BUFFER[FREEABLE[SEPARATE[OUTSIDE AVOIDS]]]]]INTERFERENCE.
  pose proof(gateway_word_context_ambient _ _ _ _ _ _ _ _ _ _ _ INPUT INTERFERENCE)as NEXT.
  destruct INPUT as[SIDE REST].
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)
    as[NEXT_SIDE[[RETAIN_NATIVE RETAIN_STABLE]FRAME]].
  split;[exact NEXT|]. split.
  - apply RETAIN_NATIVE;[|exact BUFFER].
    eapply Mem.perm_valid_block with(ofs:=0)(k:=Cur)(p:=Freeable);apply FREEABLE;lia.
  - split;[|repeat split;assumption]. intros position RANGE.
    eapply Mem.perm_unchanged_on;[exact FRAME| |apply FREEABLE;exact RANGE].
    split;[left;exact BUFFER|unfold gateway_native_no_output;tauto].
Qed.

Lemma gateway_word_readonly_stable buffer stream_block stream_offset stream output output_offset readonly
    original memory world width :
  gateway_word_scratch_context buffer stream_block stream_offset stream output output_offset readonly original memory world ->
  forall object position,gateway_word_scratch_readonly buffer width output output_offset readonly object position ->
    stable_readonly world object position.
Proof.
  intros[[SIDE[STREAM[OUTPUT[READONLY RAW]]]][BUFFER REST]]object position[READ|[[SAME RANGE]|[SAME RANGE]]].
  - apply READONLY;exact READ.
  - subst object;eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact OUTPUT].
  - subst object;eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact BUFFER].
Qed.

End WordContext.
