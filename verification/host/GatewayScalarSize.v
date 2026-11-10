(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual scalar lengths decode the received bytes and retain their source tag. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueStack GatewayValueSlotSwap
  GatewayValueRegions GatewayValueTag GatewayScalarLength GatewayScalarSizeCall GatewayValueBindings GatewayBindings
  GatewayWordActual GatewayWordContext GatewayWordValues GatewayStreamWord GatewayNativeRoots GatewayWordsMemory
  GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Theorem gateway_actual_scalar_size {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    scalar slots arguments initial stream_block stream_offset final_stream readonly original before world events value after next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_tagged native stable discipline slots stream_block stream_offset final_stream readonly original
    (Int64.repr(gateway_scalar_code scalar))before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists parameters bytes prefix reading suffix word_before word_world word_after word_next size_stream,
    events=prefix++reading++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    parameters!_stream=Some(gateway_value_stream arguments) /\parameters!_depth=Some(Vint(gateway_value_depth arguments)) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)prefix
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_scalar_size_arguments scalar slots arguments))
        (gateway_value_scalar_size_cont slots parameters)word_before)word_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_scalar_size_arguments scalar slots arguments))
        Kstop word_before)word_world)reading(gateway_live(Returnstate(Vint Int.zero)Kstop word_after)word_next) /\
    gateway_received_bytes io(stream_descriptor final_stream)reading=bytes /\
    Z.of_nat(length bytes)=Int.unsigned(gateway_scalar_width scalar) /\
    Mem.loadv Mint64 word_after(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=
      Some(Vlong(Int64.repr(gateway_decoded_value bytes))) /\
    gateway_stream_read_after final_stream(Int.unsigned(gateway_scalar_width scalar))size_stream /\
    gateway_value_tagged native stable discipline slots stream_block stream_offset size_stream readonly original
      (Int64.repr(gateway_scalar_code scalar))word_after word_next /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)word_after)word_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM INPUT RUN NONNULL.
  pose proof actual_gateway_value_functions as VALUES.
  inversion VALUES as[|? ?[symbol[SYMBOL FUNCTION]]REST_VALUES];subst.
  set(property:=gateway_value_tagged native stable discipline slots stream_block stream_offset final_stream readonly original
    (Int64.repr(gateway_scalar_code scalar))).
  pose proof(gateway_value_tagged_ambient backend io native stable discipline thread_errno runtime
    slots stream_block stream_offset final_stream readonly original(Int64.repr(gateway_scalar_code scalar)))as CLOSED.
  destruct(gateway_actual_scalar_size_call backend(Clight.globalenv prog)property scalar slots arguments initial before world
    events value after next symbol stream_block stream_offset CLOSED STREAM ltac:(intros;exact(proj2 H))SYMBOL FUNCTION INPUT RUN NONNULL)
    as(parameters &prefix &reading &suffix &word_before &word_world &word_after &word_next &
      EVENTS &QUIET &STREAM_PARAMETER &DEPTH_PARAMETER &PREFIX &READY &WORD_RUN &SUFFIX).
  pose proof(gateway_value_active_swap native stable discipline slots stream_block stream_offset final_stream readonly original
    word_before word_world(proj1 READY))as SWAPPED.
  pose proof(gateway_value_active_tag_context backend io native stable discipline thread_errno runtime
    (gateway_value_swap_slots slots)stream_block stream_offset final_stream readonly original word_before word_world SWAPPED)as WORD_INPUT.
  destruct(gateway_actual_word backend io native stable
    (fun mode memory current=>discipline mode memory current /\
      gateway_native_roots native[gateway_value_tag_slot slots]memory current)thread_errno
    (gateway_thread_with_native_roots backend io native stable discipline thread_errno runtime[gateway_value_tag_slot slots])
    (gateway_value_scalar_size_arguments scalar slots arguments)word_before word_world reading word_after word_next
    stream_block stream_offset final_stream(gateway_value_size_slot slots)Ptrofs.zero
    (gateway_value_keep_size(gateway_value_swap_slots slots)readonly)word_before
    STREAM eq_refl WORD_INPUT WORD_RUN)
    as(bytes &size_stream &WIDTH &COUNT &OBSERVED &LOAD &STREAM_AFTER &FINAL_CONTEXT).
  pose proof(gateway_value_tag_context_active native stable discipline(gateway_value_swap_slots slots)
    stream_block stream_offset final_stream size_stream readonly original word_before word_world word_after word_next
    SWAPPED FINAL_CONTEXT)as SWAPPED_AFTER.
  pose proof(gateway_value_active_swap native stable discipline(gateway_value_swap_slots slots)
    stream_block stream_offset size_stream readonly original word_after word_next SWAPPED_AFTER)as ACTIVE.
  rewrite gateway_value_slots_involution in ACTIVE.
  destruct FINAL_CONTEXT as(SIDE &STREAM_NATIVE &OUTPUT_NATIVE &READONLY_STABLE &RAW &FRAME).
  assert(TAG:Mem.loadv Mint64 word_after(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=
    Some(Vlong(Int64.repr(gateway_scalar_code scalar)))).
  { change(Mem.load Mint64 word_after(gateway_value_tag_slot slots)0=
      Some(Vlong(Int64.repr(gateway_scalar_code scalar)))).
    pose proof(proj2 READY)as BEFORE_TAG.
    change(Mem.load Mint64 word_before(gateway_value_tag_slot slots)0=
      Some(Vlong(Int64.repr(gateway_scalar_code scalar))))in BEFORE_TAG.
    eapply Mem.load_unchanged_on;[exact FRAME| |exact BEFORE_TAG].
    intros position RANGE;right;split;[reflexivity|exact RANGE]. }
  exists parameters,bytes,prefix,reading,suffix,word_before,word_world,word_after,word_next,size_stream.
  split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact STREAM_PARAMETER|]. split;[exact DEPTH_PARAMETER|].
  split;[exact PREFIX|]. split;[exact WORD_RUN|]. split;[exact OBSERVED|]. split;[exact COUNT|].
  split;[exact LOAD|]. split;[exact STREAM_AFTER|]. split;[split;[exact ACTIVE|exact TAG]|exact SUFFIX].
Qed.
