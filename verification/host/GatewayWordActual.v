(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual maintained word caller consumes its proved native reader. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadyActual GatewayWordComplete GatewayWordValues
  GatewayWordContext GatewayStreamWord GatewayStreamInterface GatewayThreadRuntime GatewayBindings GatewayValueBindings.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_word {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    arguments before world events after next stream_block stream_offset initial output output_offset readonly original :
  word_stream arguments=Vptr stream_block stream_offset ->word_output arguments=Vptr output output_offset ->
  gateway_word_context native stable discipline stream_block stream_offset initial output output_offset readonly original before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists bytes final_stream,
    Int.unsigned(word_width arguments)<=8 /\Z.of_nat(length bytes)=Int.unsigned(word_width arguments) /\
    gateway_received_bytes io(stream_descriptor initial)events=bytes /\
    Mem.loadv Mint64 after(Vptr output output_offset)=Some(Vlong(Int64.repr(gateway_decoded_value bytes))) /\
    gateway_stream_read_after initial(Int.unsigned(word_width arguments))final_stream /\
    gateway_word_context native stable discipline stream_block stream_offset final_stream output output_offset readonly original after next.
Proof.
  intros STREAM OUTPUT INPUT RUN.
  pose proof actual_gateway_transfer_functions as TRANSFER.
  pose proof actual_gateway_value_functions as VALUES.
  inversion TRANSFER as[|? ?[read_symbol[READ_SYMBOL READ_FUNCTION]]REST];subst.
  inversion VALUES as[|? ?[word_symbol[WORD_SYMBOL WORD_FUNCTION]]REST_VALUE];subst.
  inversion REST_VALUE as[|? ?[get_symbol[GET_SYMBOL GET_FUNCTION]]END];subst.
  exact(gateway_actual_word_complete backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    (gateway_actual_complete_read backend io native stable discipline thread_errno runtime)
    arguments before world events after next read_symbol get_symbol stream_block stream_offset initial output output_offset
    readonly original STREAM OUTPUT READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION INPUT RUN).
Qed.
