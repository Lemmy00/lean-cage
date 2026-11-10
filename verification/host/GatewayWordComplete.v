(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Exact byte provenance and retained writable inputs describe the same word execution. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayStreamUnique GatewayStreamWord
  GatewayWordContext GatewayWordSource GatewayWordOwned GatewayWordValues GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_word_complete {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int)
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (read_source:gateway_read_source_producer backend ge io native stable(discipline None))
    arguments before world events after next read_symbol get_symbol stream_block stream_offset initial
    output output_offset readonly original :
  word_stream arguments=Vptr stream_block stream_offset ->word_output arguments=Vptr output output_offset ->
  Genv.find_symbol ge _host_read=Some read_symbol ->Genv.find_funct_ptr ge read_symbol=Some(Internal f_host_read) ->
  Genv.find_symbol ge _host_get64=Some get_symbol ->Genv.find_funct_ptr ge get_symbol=Some(Internal f_host_get64) ->
  gateway_word_context native stable discipline stream_block stream_offset initial output output_offset readonly original before world ->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists bytes final_stream,
    Int.unsigned(word_width arguments)<=8 /\Z.of_nat(length bytes)=Int.unsigned(word_width arguments) /\
    gateway_received_bytes io(stream_descriptor initial)events=bytes /\
    Mem.loadv Mint64 after(Vptr output output_offset)=Some(Vlong(Int64.repr(gateway_decoded_value bytes))) /\
    gateway_stream_read_after initial(Int.unsigned(word_width arguments))final_stream /\
    gateway_word_context native stable discipline stream_block stream_offset final_stream
      output output_offset readonly original after next.
Proof.
  intros STREAM OUTPUT READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION INPUT RUN.
  destruct(gateway_word_actual_decode backend ge io native stable discipline thread_errno runtime read_source
    arguments before world events after next read_symbol get_symbol stream_block stream_offset initial output output_offset
    readonly original STREAM OUTPUT READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION INPUT RUN)
    as(prefix &reading &suffix &bytes &decoded_stream &EVENTS &WIDTH &COUNT &READ_OBSERVED &OBSERVED &LOAD &
      DECODED_MEMORY &DECODED_AFTER &SIDE &STREAM_NATIVE &OUTPUT_NATIVE &FRAME).
  destruct(gateway_actual_word_retains_context backend ge io native stable discipline thread_errno runtime read_source
    arguments before world events after next read_symbol get_symbol stream_block stream_offset initial output output_offset
    readonly original STREAM OUTPUT READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION INPUT RUN)
    as(final_stream &STREAM_AFTER &FINAL).
  exists bytes,final_stream.
  split;[exact WIDTH|]. split;[exact COUNT|]. split;[exact OBSERVED|]. split;[exact LOAD|].
  split;[exact STREAM_AFTER|exact FINAL].
Qed.
