(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real tag byte reaches dispatch with the caller's remaining writable cells intact. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueTag
  GatewayValueFirstWord GatewayValueStack GatewayValueNodeMemory GatewayWordComplete GatewayWordContext GatewayWordValues
  GatewayStreamInterface GatewayStreamLayout GatewayStreamWord GatewayThreadRuntime GatewayNativeRoots.
Import ListNotations.
Open Scope Z_scope.

Section ValueTagOwned.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (read_source:forall held,gateway_read_source_producer backend ge io native stable
    (fun memory world=>discipline None memory world /\gateway_native_roots native held memory world)).

Theorem gateway_actual_value_owned_tag arguments before world events value after next
    stream_block stream_offset initial readonly original word_symbol read_symbol get_symbol :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->stream_member_layout ge _nodes 32 ->
  Genv.find_symbol ge _host_word=Some word_symbol ->Genv.find_funct_ptr ge word_symbol=Some(Internal f_host_word) ->
  Genv.find_symbol ge _host_read=Some read_symbol ->Genv.find_funct_ptr ge read_symbol=Some(Internal f_host_read) ->
  Genv.find_symbol ge _host_get64=Some get_symbol ->Genv.find_funct_ptr ge get_symbol=Some(Internal f_host_get64) ->
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists slots byte prefix reading suffix word_before word_world word_after word_next final_stream,
    events=prefix++reading++suffix /\gateway_value_depth arguments<>Int.zero /\stream_nodes initial<>Int64.zero /\
    Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_tag_arguments slots arguments))
        (gateway_value_tag_cont slots arguments initial)word_before)word_world) /\
    gateway_value_allocated native stable discipline slots stream_block stream_offset
      (gateway_stream_node_debit initial)readonly original word_before word_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_tag_arguments slots arguments))
        Kstop word_before)word_world)reading
      (gateway_live(Returnstate(Vint Int.zero)Kstop word_after)word_next) /\
    gateway_received_bytes io(stream_descriptor initial)reading=[byte] /\
    Mem.loadv Mint64 word_after(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=
      Some(Vlong(Int64.repr(Byte.unsigned byte))) /\
    gateway_stream_read_after(gateway_stream_node_debit initial)1 final_stream /\
    gateway_value_active native stable discipline slots stream_block stream_offset final_stream readonly original word_after word_next /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)word_after)word_next)
      suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM LAYOUT WORD_SYMBOL WORD_FUNCTION READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION INPUT RUN NONNULL.
  destruct(gateway_actual_value_first_word backend ge io native stable discipline thread_errno runtime
    arguments before world events value after next stream_block stream_offset initial readonly original word_symbol
    STREAM LAYOUT WORD_SYMBOL WORD_FUNCTION INPUT RUN NONNULL)
    as(slots &prefix &reading &suffix &word_before &word_world &word_after &word_next &
      EVENTS &DEPTH &NODES &QUIET &TO_WORD &WORD_READY &WORD_RUN &REST).
  pose proof(gateway_value_allocated_active native stable discipline slots stream_block stream_offset
    (gateway_stream_node_debit initial)readonly original word_before word_world WORD_READY)as ACTIVE.
  pose proof(gateway_value_active_tag_context backend io native stable discipline thread_errno runtime
    slots stream_block stream_offset(gateway_stream_node_debit initial)readonly original word_before word_world ACTIVE)
    as WORD_INPUT.
  destruct(gateway_actual_word_complete backend ge io native stable
    (fun mode memory world=>discipline mode memory world /\
      gateway_native_roots native[gateway_value_size_slot slots]memory world)thread_errno
    (gateway_thread_with_native_roots backend io native stable discipline thread_errno runtime[gateway_value_size_slot slots])
    (read_source[gateway_value_size_slot slots])
    (gateway_value_tag_arguments slots arguments)word_before word_world reading word_after word_next read_symbol get_symbol
    stream_block stream_offset(gateway_stream_node_debit initial)(gateway_value_tag_slot slots)Ptrofs.zero
    (gateway_value_keep_size slots readonly)word_before
    STREAM eq_refl READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION WORD_INPUT WORD_RUN)
    as(bytes &final_stream &WIDTH &COUNT &OBSERVED &LOAD &STREAM_AFTER &FINAL_CONTEXT).
  change(Z.of_nat(length bytes)=1)in COUNT.
  destruct bytes as[|byte bytes];[cbn in COUNT;lia|].
  destruct bytes as[|other bytes];[|cbn in COUNT;lia].
  rewrite gateway_decoded_single in LOAD.
  pose proof(gateway_value_tag_context_active native stable discipline slots stream_block stream_offset
    (gateway_stream_node_debit initial)final_stream readonly original word_before word_world word_after word_next
    ACTIVE FINAL_CONTEXT)as FINAL_ACTIVE.
  exists slots,byte,prefix,reading,suffix,word_before,word_world,word_after,word_next,final_stream.
  split;[exact EVENTS|]. split;[exact DEPTH|]. split;[exact NODES|]. split;[exact QUIET|].
  split;[exact TO_WORD|]. split;[exact WORD_READY|]. split;[exact WORD_RUN|].
  split;[exact OBSERVED|]. split;[exact LOAD|]. split;[exact STREAM_AFTER|]. split;assumption.
Qed.

End ValueTagOwned.
