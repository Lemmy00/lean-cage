(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A container count follows its same actual successful four-byte word call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayValueGuards
  GatewayValueTag GatewayValueNull GatewayValueDispatch GatewayValueAfterBoolean GatewayContainerLength GatewayCheckedWord
  GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime GatewayStreamWord GatewayValueWord.
From HostGateway Require Import GatewayValueStack GatewayValueSlotSwap GatewayValueRegions GatewayValueBindings GatewayBindings
  GatewayWordActual GatewayWordContext GatewayWordValues GatewayNativeRoots GatewayWordsMemory
  GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Theorem gateway_actual_container_count_call {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:Memory.mem->World->Prop)container slots arguments initial before world events value after next
    symbol stream_block stream_offset :
  gateway_ambient_closed backend property ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  (forall memory current,property memory current ->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr(gateway_container_code container)))) ->
  Genv.find_symbol ge _host_word=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_word) ->
  property before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists parameters prefix reading suffix word_before word_world word_after word_next,
    events=prefix++reading++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    parameters!_stream=Some(gateway_value_stream arguments) /\parameters!_depth=Some(Vint(gateway_value_depth arguments)) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)prefix
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_container_size_arguments slots arguments))
        (gateway_value_container_size_cont slots parameters)word_before)word_world) /\property word_before word_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_container_size_arguments slots arguments))
        Kstop word_before)word_world)reading(gateway_live(Returnstate(Vint Int.zero)Kstop word_after)word_next) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)word_after)word_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED STREAM LOADED SYMBOL FUNCTION GOOD RUN NONNULL.
  destruct(gateway_container_length_owned_path backend ge property container slots arguments initial before symbol stream_block stream_offset
    CLOSED STREAM LOADED SYMBOL FUNCTION)as(parameters &LENGTH_PATH &STREAM_PARAMETER &DEPTH_PARAMETER).
  assert(PATH:gateway_source_path backend ge(Internal f_host_word)
    (gateway_word_values(gateway_value_container_size_arguments slots arguments))
    (gateway_value_container_size_cont slots parameters)property
    (Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)property).
  { eapply gateway_segment_then_call.
    - exact(gateway_value_nonzero_tag_segment backend ge property slots arguments initial before
        (Int64.repr(gateway_container_code container))CLOSED ltac:(destruct container;discriminate)LOADED).
    - eapply gateway_segment_then_call.
      + exact(gateway_value_nonboolean_segment backend ge property slots arguments initial before
          (Int64.repr(gateway_container_code container))CLOSED ltac:(destruct container;discriminate)
          ltac:(destruct container;discriminate)LOADED).
      + exact LENGTH_PATH. }
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next GOOD RUN)
    as(prefix &rest &word_before &word_world &EVENTS &QUIET &PREFIX &WORD_READY &FROM_WORD).
  destruct(gateway_return_cut backend ge(Internal f_host_word)
    (gateway_word_values(gateway_value_container_size_arguments slots arguments))(gateway_value_container_size_cont slots parameters)
    word_before word_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_WORD)
    as(reading &suffix &word_value &word_after &word_next &REST_EVENTS &WORD_RUN &REST).
  assert(ZERO:word_value=Vint Int.zero).
  { exact(gateway_checked_word_result backend ge _t'27 f_host_value(gateway_value_environment slots)parameters
      (Kseq gateway_value_container_after_size(Kseq gateway_value_after_container Kstop))word_after word_next suffix word_value value after next
      gateway_value_pointer_return eq_refl(gateway_actual_word_return_type backend ge _ _ _ _ _ _ _ WORD_RUN)NONNULL REST). }
  subst word_value.
  exists parameters,prefix,reading,suffix,word_before,word_world,word_after,word_next.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|].
  split;[exact STREAM_PARAMETER|]. split;[exact DEPTH_PARAMETER|]. split;[exact PREFIX|].
  split;[exact WORD_READY|]. split;assumption.
Qed.

Theorem gateway_actual_container_count {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    container slots arguments initial stream_block stream_offset final_stream readonly original before world events value after next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_tagged native stable discipline slots stream_block stream_offset final_stream readonly original
    (Int64.repr(gateway_container_code container))before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists parameters bytes prefix reading suffix word_before word_world word_after word_next size_stream,
    events=prefix++reading++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    parameters!_stream=Some(gateway_value_stream arguments) /\parameters!_depth=Some(Vint(gateway_value_depth arguments)) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)prefix
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_container_size_arguments slots arguments))
        (gateway_value_container_size_cont slots parameters)word_before)word_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_container_size_arguments slots arguments))
        Kstop word_before)word_world)reading(gateway_live(Returnstate(Vint Int.zero)Kstop word_after)word_next) /\
    gateway_received_bytes io(stream_descriptor final_stream)reading=bytes /\
    Z.of_nat(length bytes)=Int.unsigned(Int.repr 4) /\
    Mem.loadv Mint64 word_after(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=
      Some(Vlong(Int64.repr(gateway_decoded_value bytes))) /\
    gateway_stream_read_after final_stream(Int.unsigned(Int.repr 4))size_stream /\
    gateway_value_tagged native stable discipline slots stream_block stream_offset size_stream readonly original
      (Int64.repr(gateway_container_code container))word_after word_next /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)word_after)word_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM INPUT RUN NONNULL.
  pose proof actual_gateway_value_functions as VALUES.
  inversion VALUES as[|? ?[symbol[SYMBOL FUNCTION]]REST_VALUES];subst.
  set(property:=gateway_value_tagged native stable discipline slots stream_block stream_offset final_stream readonly original
    (Int64.repr(gateway_container_code container))).
  pose proof(gateway_value_tagged_ambient backend io native stable discipline thread_errno runtime
    slots stream_block stream_offset final_stream readonly original(Int64.repr(gateway_container_code container)))as CLOSED.
  destruct(gateway_actual_container_count_call backend(Clight.globalenv prog)property container slots arguments initial before world
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
    (gateway_value_container_size_arguments slots arguments)word_before word_world reading word_after word_next
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
    Some(Vlong(Int64.repr(gateway_container_code container)))).
  { change(Mem.load Mint64 word_after(gateway_value_tag_slot slots)0=
      Some(Vlong(Int64.repr(gateway_container_code container)))).
    pose proof(proj2 READY)as BEFORE_TAG.
    change(Mem.load Mint64 word_before(gateway_value_tag_slot slots)0=
      Some(Vlong(Int64.repr(gateway_container_code container))))in BEFORE_TAG.
    eapply Mem.load_unchanged_on;[exact FRAME| |exact BEFORE_TAG].
    intros position RANGE;right;split;[reflexivity|exact RANGE]. }
  exists parameters,bytes,prefix,reading,suffix,word_before,word_world,word_after,word_next,size_stream.
  split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact STREAM_PARAMETER|]. split;[exact DEPTH_PARAMETER|].
  split;[exact PREFIX|]. split;[exact WORD_RUN|]. split;[exact OBSERVED|]. split;[exact COUNT|].
  split;[exact LOAD|]. split;[exact STREAM_AFTER|]. split;[split;[exact ACTIVE|exact TAG]|exact SUFFIX].
Qed.
