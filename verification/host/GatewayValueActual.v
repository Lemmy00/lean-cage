(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual dispatch consumes the maintained read proof at its derived owned-root context. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadyActual GatewayBindings GatewayValueBindings
  GatewayNativeRoots GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueTag GatewayValueTagOwned
  GatewayValueNodeMemory GatewayStreamLayout GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Theorem gateway_value_actual_reads {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno) :
  forall held,gateway_read_source_producer backend(Clight.globalenv prog)io native stable
    (fun memory world=>discipline None memory world /\gateway_native_roots native held memory world).
Proof.
  intro held;exact(gateway_actual_complete_read backend io native stable
    (gateway_native_root_discipline native discipline held)thread_errno
    (gateway_thread_with_native_roots backend io native stable discipline thread_errno runtime held)).
Qed.

Theorem gateway_actual_value_tag {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    arguments before world events value after next stream_block stream_offset initial readonly original :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists slots byte prefix reading suffix word_before word_world word_after word_next final_stream,
    events=prefix++reading++suffix /\gateway_value_depth arguments<>Int.zero /\stream_nodes initial<>Int64.zero /\
    Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_word)(GatewayStreamWord.gateway_word_values(gateway_value_tag_arguments slots arguments))
        (gateway_value_tag_cont slots arguments initial)word_before)word_world) /\
    gateway_value_allocated native stable discipline slots stream_block stream_offset
      (gateway_stream_node_debit initial)readonly original word_before word_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_word)(GatewayStreamWord.gateway_word_values(gateway_value_tag_arguments slots arguments))
        Kstop word_before)word_world)reading
      (gateway_live(Returnstate(Vint Int.zero)Kstop word_after)word_next) /\
    gateway_received_bytes io(stream_descriptor initial)reading=[byte] /\
    Mem.loadv Mint64 word_after(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=
      Some(Vlong(Int64.repr(Byte.unsigned byte))) /\
    gateway_stream_read_after(gateway_stream_node_debit initial)1 final_stream /\
    gateway_value_active native stable discipline slots stream_block stream_offset final_stream readonly original word_after word_next /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)word_after)word_next)
      suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM INPUT RUN NONNULL.
  pose proof actual_gateway_transfer_functions as TRANSFER.
  pose proof actual_gateway_value_functions as VALUES.
  inversion TRANSFER as[|? ?[read_symbol[READ_SYMBOL READ_FUNCTION]]REST];subst.
  inversion VALUES as[|? ?[word_symbol[WORD_SYMBOL WORD_FUNCTION]]REST_VALUE];subst.
  inversion REST_VALUE as[|? ?[get_symbol[GET_SYMBOL GET_FUNCTION]]END];subst.
  destruct actual_stream_layout as(_ & _ & _ & _ & _ & _ &NODES & _).
  exact(gateway_actual_value_owned_tag backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    (gateway_value_actual_reads backend io native stable discipline thread_errno runtime)
    arguments before world events value after next stream_block stream_offset initial readonly original
    word_symbol read_symbol get_symbol STREAM NODES WORD_SYMBOL WORD_FUNCTION READ_SYMBOL READ_FUNCTION
    GET_SYMBOL GET_FUNCTION INPUT RUN NONNULL).
Qed.
