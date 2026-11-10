(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Scalar success contains its same successful payload read. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayValueGuards
  GatewayScalarLength GatewayScalarAllocationPath GatewayScalarBuffer GatewayScalarReadPath GatewayCheckedCalls
  GatewaySourcePaths GatewayReturnTypes GatewayBindings GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.

Theorem gateway_actual_scalar_payload_call {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots arguments parameters stream_block stream_offset initial readonly original size object
    before world events value after next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_value_scalar_malloc_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists called_parameters prefix reading suffix read_before read_world read_after read_next,
    events=prefix++reading++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_stream=Some(gateway_value_stream arguments) /\called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_value_scalar_malloc_cont slots parameters)before)world)prefix
      (gateway_live(Callstate(Internal f_host_read)[gateway_value_stream arguments;Vptr object Ptrofs.zero;Vlong size]
        (gateway_scalar_read_cont slots called_parameters)read_before)read_world) /\
    gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
      original size object read_before read_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_read)[gateway_value_stream arguments;Vptr object Ptrofs.zero;Vlong size]Kstop
        read_before)read_world)reading(gateway_live(Returnstate(Vint Int.zero)Kstop read_after)read_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots called_parameters)read_after)read_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM STREAM_PARAMETER INPUT RUN NONNULL.
  pose proof actual_gateway_transfer_functions as BINDINGS.
  inversion BINDINGS as[|? ?[symbol[SYMBOL FUNCTION]]REST_BINDINGS];subst.
  destruct(gateway_scalar_payload_read_path backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    heap_allocation scalar slots arguments parameters stream_block stream_offset initial readonly original size object before symbol
    STREAM STREAM_PARAMETER SYMBOL FUNCTION)as(called_parameters &PATH &CALLED_STREAM &CALLED_BYTES).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &read_before &read_world &EVENTS &QUIET &PREFIX &READY &FROM_READ).
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_read)
    [gateway_value_stream arguments;Vptr object Ptrofs.zero;Vlong size](gateway_scalar_read_cont slots called_parameters)
    read_before read_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_READ)
    as(reading &suffix &read_value &read_after &read_next &REST_EVENTS &READ_RUN &REST).
  assert(ZERO:read_value=Vint Int.zero).
  { rewrite gateway_scalar_read_checked in REST.
    exact(gateway_checked_call_result backend(Clight.globalenv prog)_t'11 f_host_value(gateway_value_environment slots)
      called_parameters gateway_scalar_read_failure(Kseq gateway_scalar_after_read(Kseq gateway_value_after_scalar Kstop))
      read_after read_next suffix read_value value after next gateway_value_pointer_return gateway_scalar_read_failure_null eq_refl
      (actual_host_read_return_type backend(Clight.globalenv prog)_ _ _ _ _ _ _ READ_RUN)NONNULL REST). }
  subst read_value.
  exists called_parameters,prefix,reading,suffix,read_before,read_world,read_after,read_next.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact CALLED_STREAM|].
  split;[exact CALLED_BYTES|]. split;[exact PREFIX|]. split;[exact READY|]. split;assumption.
Qed.
