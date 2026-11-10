(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Scalar payload bytes come from the same actual bounded response read. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarLength GatewayScalarAllocationPath
  GatewayScalarBuffer GatewayScalarReadPath GatewayScalarReadCall GatewayScalarReadMemory GatewayScalarReadReceipt
  GatewayStreamInterface GatewayThreadRuntime GatewayReadyActual.
Import ListNotations.

Theorem gateway_actual_scalar_payload {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots arguments parameters stream_block stream_offset initial readonly original size object
    before world events value after next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_value_scalar_malloc_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists called_parameters prefix reading suffix read_before read_world read_after read_next bytes final_stream,
    events=prefix++reading++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_stream=Some(gateway_value_stream arguments) /\called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_read)[gateway_value_stream arguments;Vptr object Ptrofs.zero;Vlong size]Kstop
        read_before)read_world)reading(gateway_live(Returnstate(Vint Int.zero)Kstop read_after)read_next) /\
    gateway_read_receipt io read_before stream_block stream_offset initial object Ptrofs.zero(Int64.unsigned size)
      (gateway_scalar_payload_readonly slots object size readonly)reading read_after bytes /\
    gateway_stream_read_after initial(Int64.unsigned size)final_stream /\
    gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset final_stream readonly
      original size object read_after read_next /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots called_parameters)read_after)read_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM STREAM_PARAMETER INPUT RUN NONNULL.
  destruct(gateway_actual_scalar_payload_call backend io native stable discipline thread_errno runtime
    heap_allocation scalar slots arguments parameters stream_block stream_offset initial readonly original size object
    before world events value after next STREAM STREAM_PARAMETER INPUT RUN NONNULL)
    as(called_parameters &prefix &reading &suffix &read_before &read_world &read_after &read_next &
      EVENTS &QUIET &CALLED_STREAM &CALLED_BYTES &PREFIX &READY &READ_RUN &REST).
  pose proof READY as[[[[[SIDE[STREAM_NATIVE CONTEXT]]SLOTS]TAG_LOAD]SIZE_LOAD][HEAP SEPARATE]].
  destruct HEAP as[HEAP_SIDE[BUFFER_NATIVE HEAP_REST]].
  destruct(gateway_actual_complete_read backend io native stable discipline thread_errno runtime
    read_before read_world stream_block stream_offset initial object Ptrofs.zero(Int64.unsigned size)
    (gateway_scalar_payload_readonly slots object size readonly)reading read_after read_next
    SIDE STREAM_NATIVE BUFFER_NATIVE
    (gateway_scalar_payload_stable backend io native stable discipline thread_errno runtime heap_allocation scalar slots
      stream_block stream_offset initial readonly original size object read_before read_world READY)
    (gateway_scalar_payload_inputs native stable discipline heap_allocation scalar slots stream_block stream_offset initial
      readonly original size object read_before read_world READY)
    ltac:(rewrite Int64.repr_unsigned;rewrite<-STREAM;exact READ_RUN))
    as(bytes &RECEIPT &AFTER_SIDE &AFTER_STREAM &AFTER_BUFFER &AFTER_STABLE &RETAIN_NATIVE &RETAIN_STABLE).
  destruct(gateway_scalar_payload_receipt io native stable discipline heap_allocation scalar slots stream_block stream_offset initial
    readonly original size object read_before read_world reading read_after read_next bytes READY RECEIPT AFTER_SIDE AFTER_STREAM
    AFTER_BUFFER AFTER_STABLE(conj RETAIN_NATIVE RETAIN_STABLE))as(final_stream &STREAM_AFTER &FINAL).
  exists called_parameters,prefix,reading,suffix,read_before,read_world,read_after,read_next,bytes,final_stream.
  split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact CALLED_STREAM|]. split;[exact CALLED_BYTES|].
  split;[exact READ_RUN|]. split;[exact RECEIPT|]. split;[exact STREAM_AFTER|]. split;[exact FINAL|exact REST].
Qed.
