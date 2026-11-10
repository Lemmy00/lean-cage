(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual tag9 caller cuts one same helper execution and
   its real payload cleanup; a nonnull outer result forces that helper result nonnull. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayScalarLength GatewayScalarContext
  GatewayScalarReadPath GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarBytesPath GatewayScalarNumberPath GatewayScalarCleanup
  GatewaySourcePaths GatewaySourceSegments GatewayBindings GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Theorem gateway_actual_number_constructor_cut {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next:
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->
  gateway_scalar_payload_ready native stable discipline heap_allocation gateway_scalar_number slots stream_block stream_offset initial readonly
    original size object bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists called_parameters prefix constructing suffix constructor_before constructor_world constructor_after constructor_next,
    events=prefix++constructing++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_number slots stream_block stream_offset initial
      readonly original size object bytes constructor_before constructor_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_json_number)[Vptr object Ptrofs.zero;Vlong size]Kstop constructor_before)constructor_world)constructing
      (gateway_live(Returnstate value Kstop constructor_after)constructor_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate value(gateway_scalar_constructor_cont _t'20 slots called_parameters)constructor_after)constructor_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros BUFFER INPUT RUN NONNULL.
  destruct(gateway_actual_function_binding _host_json_number(Internal f_host_json_number)ltac:(vm_compute;reflexivity))as[symbol[SYMBOL FUNCTION]].
  destruct(gateway_scalar_number_path backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes before symbol
    BUFFER SYMBOL FUNCTION)as(called_parameters &BYTES_PATH &CALLED_BUFFER).
  pose proof(gateway_scalar_terminator_segment backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    heap_allocation gateway_scalar_number slots parameters stream_block stream_offset initial readonly original size object bytes before BUFFER)as TERMINATE.
  pose proof(gateway_segment_then_call backend(Clight.globalenv prog)_ _ _ _ _ _ _ _ TERMINATE BYTES_PATH)as PATH.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &constructor_before &constructor_world &EVENTS &QUIET &PREFIX &READY &FROM_CONSTRUCTOR).
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_json_number)[Vptr object Ptrofs.zero;Vlong size]
    (gateway_scalar_constructor_cont _t'20 slots called_parameters)constructor_before constructor_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_CONSTRUCTOR)
    as(constructing &suffix &returned &constructor_after &constructor_next &REST_EVENTS &CONSTRUCTOR_RUN &REST).
  pose proof(proj1(gateway_actual_scalar_cleanup_cut backend _t'20 slots called_parameters object constructor_after constructor_next suffix
    returned value after next ltac:(discriminate)CALLED_BUFFER REST))as SAME;subst returned.
  exists called_parameters,prefix,constructing,suffix,constructor_before,constructor_world,constructor_after,constructor_next.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|].
  split;[exact CALLED_BUFFER|]. split;[exact READY|]. split;assumption.
Qed.
