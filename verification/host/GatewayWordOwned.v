(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A returned word reader retains the actual caller's next writable inputs. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayWordContext GatewayWordInputs GatewayWordSource
  GatewayWordReadReceipt GatewayWordRuntime GatewayWordPermissions GatewayFrames GatewayStreamMemory GatewayWordsMemory
  GatewayStreamInterface GatewayStreamWord GatewayThreadRuntime GatewayReadonlyRuntime GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section WordOwned.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (read_source:gateway_read_source_producer backend ge io native stable(discipline None)).

Theorem gateway_actual_word_retains_context arguments before world events after next read_symbol get_symbol
    stream_block stream_offset initial output output_offset readonly original :
  word_stream arguments=Vptr stream_block stream_offset ->word_output arguments=Vptr output output_offset ->
  Genv.find_symbol ge _host_read=Some read_symbol ->Genv.find_funct_ptr ge read_symbol=Some(Internal f_host_read) ->
  Genv.find_symbol ge _host_get64=Some get_symbol ->Genv.find_funct_ptr ge get_symbol=Some(Internal f_host_get64) ->
  gateway_word_context native stable discipline stream_block stream_offset initial output output_offset readonly original before world ->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists final_stream,gateway_stream_read_after initial(Int.unsigned(word_width arguments))final_stream /\
    gateway_word_context native stable discipline stream_block stream_offset final_stream
      output output_offset readonly original after next.
Proof.
  intros STREAM OUTPUT READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION INPUT RUN.
  destruct(gateway_word_actual_read_receipt backend ge io native stable discipline thread_errno runtime read_source
    arguments before world events after next read_symbol stream_block stream_offset initial output output_offset readonly original
    STREAM OUTPUT READ_SYMBOL READ_FUNCTION INPUT RUN)
    as(buffer &prefix &reading &suffix &read_before &read_world &read_after &read_next &bytes &
      EVENTS &WIDTH &PREFIX &READ_SIDE &RECEIPT &SIDE_AFTER &STREAM_AFTER &BUFFER_AFTER &STABLE_AFTER &RETAINED &REST &QUIET).
  assert(WIDTH_RANGE:0<=Int.unsigned(word_width arguments)<=8).
  { split;[pose proof(Int.unsigned_range(word_width arguments));lia|exact WIDTH]. }
  pose proof(gateway_word_after_read_ready io native stable discipline
    buffer stream_block stream_offset initial output output_offset readonly original read_before read_world
    (Int.unsigned(word_width arguments))reading read_after read_next bytes READ_SIDE WIDTH_RANGE RECEIPT
    SIDE_AFTER STREAM_AFTER BUFFER_AFTER STABLE_AFTER RETAINED)as READY.
  pose proof RECEIPT as RECEIPT_COPY.
  destruct RECEIPT_COPY as[COUNT FITS OBSERVED LOADED DATA_PERMS STREAM_PERMS[final_stream[FINAL_STREAM READ_AFTER]]READ_FRAME].
  assert(BYTE_WIDTH:(length bytes<=8)%nat)by lia.
  assert(INITIALIZED:Mem.loadbytes read_after buffer 0(Z.of_nat(length bytes))=Some(Memdata.inj_bytes bytes)).
  { rewrite COUNT;exact LOADED. }
  set(post_readonly:=gateway_word_post_readonly stream_block stream_offset readonly).
  set(post_side:=gateway_word_stage native stable discipline None buffer output[stream_block]post_readonly read_after
    (gateway_word_store_ready buffer output(Ptrofs.unsigned output_offset))).
  destruct(gateway_word_actual_get_from_read_bytes_coupled backend ge post_side buffer arguments
    read_after read_next suffix after next bytes get_symbol
    (gateway_word_stage_get_contract backend io native stable discipline thread_errno runtime
      stream_block stream_offset readonly read_after buffer output output_offset(length bytes))
    READY BYTE_WIDTH ltac:(symmetry;exact COUNT)INITIALIZED GET_SYMBOL GET_FUNCTION REST)
    as(middle &get_events &last &get_before &get_world &get_after &get_next &
      GET_EVENTS &TO_GET &GET_RUN &LAST &GET_BEFORE_SIDE &GET_AFTER_SIDE &MIDDLE_QUIET).
  destruct READ_SIDE as[CALL_SIDE[BUFFER[FREEABLE[SEPARATE[OUTSIDE AVOIDS]]]]].
  destruct CALL_SIDE as[CALL_READY[STREAM_PRIVATE[OUTPUT_PRIVATE[READONLY[RAW INITIAL_FRAME]]]]].
  destruct RAW as[RAW ALIGNED].
  destruct GET_AFTER_SIDE as[GET_RESOURCES GET_READY].
  destruct(gateway_actual_word_store_writable backend ge io native stable discipline thread_errno runtime
    None buffer arguments output output_offset _[stream_block]read_after post_readonly get_after get_next last after next
    OUTPUT ltac:(congruence)(gateway_read_data_bounds _ _ _ _ _ _ _ _ RAW)
    (gateway_word_post_readonly_output stream_block stream_offset output output_offset readonly read_before initial
      ltac:(split;assumption))
    (gateway_word_post_readonly_scratch buffer stream_block stream_offset readonly SEPARATE AVOIDS)
    GET_RESOURCES GET_READY LAST)as[FINAL_RESOURCES[LOAD OUTPUT_ACCESS]].
  destruct FINAL_RESOURCES as[FINAL_SIDE[FINAL_BUFFER[FINAL_OUTPUT[BUFFER_LIVE[OUTPUT_LIVE[HELD[OWNED FINAL_FRAME]]]]]]].
  assert(STREAM_WRITABLE:Mem.range_perm after stream_block(Ptrofs.unsigned stream_offset)
    (Ptrofs.unsigned stream_offset+48)Cur Writable).
  { intros position RANGE;eapply Mem.perm_unchanged_on;[exact FINAL_FRAME|left;split;[reflexivity|exact RANGE]|].
    apply(proj1(STREAM_PERMS position Cur Writable RANGE));apply(gateway_read_stream_owned _ _ _ _ _ _ _ _ RAW);exact RANGE. }
  assert(CALLER_FRAME:Mem.unchanged_on readonly original after).
  { eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|]. eapply Mem.unchanged_on_trans.
    - eapply Mem.unchanged_on_implies;[exact READ_FRAME|intros;left;assumption].
    - eapply Mem.unchanged_on_implies;[exact FINAL_FRAME|intros;right;assumption]. }
  exists final_stream;split;[exact READ_AFTER|].
  split;[exact FINAL_SIDE|].
  split;[exact(proj2(HELD stream_block ltac:(left;reflexivity)))|]. split;[exact FINAL_OUTPUT|].
  split.
  - intros object position READ;destruct(OWNED object position(or_intror READ))as[READABLE[NATIVE|STABLE]].
    + eapply gateway_thread_native_stable;[exact runtime|exact FINAL_SIDE|exact NATIVE].
    + exact STABLE.
  - split;[|exact CALLER_FRAME]. split;[|exact ALIGNED].
    constructor.
    + eapply gateway_stream_memory_closed;[exact(gateway_read_stream_bounds _ _ _ _ _ _ _ _ RAW)|exact FINAL_STREAM|].
      eapply Mem.unchanged_on_implies;[exact FINAL_FRAME|intros;left;assumption].
    + exact(gateway_read_amount _ _ _ _ _ _ _ _ RAW).
    + exact(gateway_read_stream_bounds _ _ _ _ _ _ _ _ RAW).
    + exact(gateway_read_data_bounds _ _ _ _ _ _ _ _ RAW).
    + exact STREAM_WRITABLE.
    + exact OUTPUT_LIVE.
    + exact(proj1 OUTPUT_ACCESS).
    + exact(gateway_read_data_separate _ _ _ _ _ _ _ _ RAW).
    + intros object position READ;destruct(OWNED object position(or_intror READ))as[READABLE CAPABILITY].
      eapply Mem.perm_valid_block;exact READABLE.
    + intros object position READ;exact(proj1(OWNED object position(or_intror READ))).
    + exact(gateway_read_readonly_data _ _ _ _ _ _ _ _ RAW).
    + exact(gateway_read_readonly_remaining _ _ _ _ _ _ _ _ RAW).
    + exact(gateway_read_readonly_cancel _ _ _ _ _ _ _ _ RAW).
Qed.

End WordOwned.
