(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A scalar success contains its same actual successful size-word call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayValueGuards
  GatewayValueTag GatewayValueNull GatewayValueDispatch GatewayValueAfterBoolean GatewayScalarLength GatewayCheckedWord
  GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime GatewayStreamWord GatewayValueWord.
Import ListNotations.

Theorem gateway_actual_scalar_size_call {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:Memory.mem->World->Prop)scalar slots arguments initial before world events value after next
    symbol stream_block stream_offset :
  gateway_ambient_closed backend property ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  (forall memory current,property memory current ->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr(gateway_scalar_code scalar)))) ->
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
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_scalar_size_arguments scalar slots arguments))
        (gateway_value_scalar_size_cont slots parameters)word_before)word_world) /\property word_before word_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_scalar_size_arguments scalar slots arguments))
        Kstop word_before)word_world)reading(gateway_live(Returnstate(Vint Int.zero)Kstop word_after)word_next) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)word_after)word_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED STREAM LOADED SYMBOL FUNCTION GOOD RUN NONNULL.
  destruct(gateway_scalar_length_owned_path backend ge property scalar slots arguments initial before symbol stream_block stream_offset
    CLOSED STREAM LOADED SYMBOL FUNCTION)as(parameters &LENGTH_PATH &STREAM_PARAMETER &DEPTH_PARAMETER).
  assert(PATH:gateway_source_path backend ge(Internal f_host_word)
    (gateway_word_values(gateway_value_scalar_size_arguments scalar slots arguments))
    (gateway_value_scalar_size_cont slots parameters)property
    (Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)property).
  { eapply gateway_segment_then_call.
    - exact(gateway_value_nonzero_tag_segment backend ge property slots arguments initial before
        (Int64.repr(gateway_scalar_code scalar))CLOSED ltac:(destruct scalar;discriminate)LOADED).
    - eapply gateway_segment_then_call.
      + exact(gateway_value_nonboolean_segment backend ge property slots arguments initial before
          (Int64.repr(gateway_scalar_code scalar))CLOSED ltac:(destruct scalar;discriminate)
          ltac:(destruct scalar;discriminate)LOADED).
      + exact LENGTH_PATH. }
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next GOOD RUN)
    as(prefix &rest &word_before &word_world &EVENTS &QUIET &PREFIX &WORD_READY &FROM_WORD).
  destruct(gateway_return_cut backend ge(Internal f_host_word)
    (gateway_word_values(gateway_value_scalar_size_arguments scalar slots arguments))(gateway_value_scalar_size_cont slots parameters)
    word_before word_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_WORD)
    as(reading &suffix &word_value &word_after &word_next &REST_EVENTS &WORD_RUN &REST).
  assert(ZERO:word_value=Vint Int.zero).
  { exact(gateway_checked_word_result backend ge _t'6 f_host_value(gateway_value_environment slots)parameters
      (Kseq gateway_value_scalar_after_size(Kseq gateway_value_after_scalar Kstop))word_after word_next suffix word_value value after next
      gateway_value_pointer_return eq_refl(gateway_actual_word_return_type backend ge _ _ _ _ _ _ _ WORD_RUN)NONNULL REST). }
  subst word_value.
  exists parameters,prefix,reading,suffix,word_before,word_world,word_after,word_next.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|].
  split;[exact STREAM_PARAMETER|]. split;[exact DEPTH_PARAMETER|]. split;[exact PREFIX|].
  split;[exact WORD_READY|]. split;assumption.
Qed.
