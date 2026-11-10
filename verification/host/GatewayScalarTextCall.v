(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same successful text branch contains its actual constructor and cleanup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayScalarLength
  GatewayScalarReadPath GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarBytesPath GatewayScalarTextPath GatewayScalarCleanup
  GatewaySourcePaths GatewaySourceSegments GatewayObjects GatewayBindings GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Theorem actual_gateway_text_binding :
  exists definition,gateway_object_api_definition gateway_api_unicode_utf8=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyUnicode_DecodeUTF8 definition /\
    type_of_fundef definition=Tfunction[tptr tschar;tlong;tptr tschar](tptr(Tstruct __object noattr))cc_default.
Proof.
  eexists;split;[vm_compute;reflexivity|]. split.
  - apply gateway_actual_function_binding;vm_compute;reflexivity.
  - reflexivity.
Qed.

Theorem gateway_actual_text_constructor_cut {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next mode_symbol :
  Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol ->
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  gateway_scalar_payload_ready native stable discipline heap_allocation gateway_scalar_text slots stream_block stream_offset initial readonly
    original size object bytes before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists definition called_parameters prefix constructing suffix constructor_before constructor_world constructor_after constructor_next,
    gateway_object_api_definition gateway_api_unicode_utf8=Some definition /\
    events=prefix++constructing++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_text slots stream_block stream_offset initial
      readonly original size object bytes constructor_before constructor_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]Kstop constructor_before)constructor_world)constructing
      (gateway_live(Returnstate value Kstop constructor_after)constructor_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate value(gateway_scalar_constructor_cont _t'21 slots called_parameters)constructor_after)constructor_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros MODE BUFFER INPUT RUN NONNULL.
  destruct actual_gateway_text_binding as(definition &DEFINITION &[symbol[SYMBOL FUNCTION]] &TYPE).
  destruct(gateway_scalar_text_path backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes before symbol definition mode_symbol
    BUFFER SYMBOL FUNCTION TYPE MODE)as(called_parameters &BYTES_PATH &CALLED_BUFFER).
  pose proof(gateway_scalar_terminator_segment backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    heap_allocation gateway_scalar_text slots parameters stream_block stream_offset initial readonly original size object bytes before BUFFER)as TERMINATE.
  pose proof(gateway_segment_then_call backend(Clight.globalenv prog)_ _ _ _ _ _ _ _ TERMINATE BYTES_PATH)as PATH.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &constructor_before &constructor_world &EVENTS &QUIET &PREFIX &READY &FROM_CONSTRUCTOR).
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]
    (gateway_scalar_constructor_cont _t'21 slots called_parameters)constructor_before constructor_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_CONSTRUCTOR)
    as(constructing &suffix &returned &constructor_after &constructor_next &REST_EVENTS &CONSTRUCTOR_RUN &REST).
  pose proof(proj1(gateway_actual_scalar_cleanup_cut backend _t'21 slots called_parameters object constructor_after constructor_next suffix
    returned value after next ltac:(discriminate)CALLED_BUFFER REST))as SAME.
  subst returned.
  exists definition,called_parameters,prefix,constructing,suffix,constructor_before,constructor_world,constructor_after,constructor_next.
  split;[exact DEFINITION|]. split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|].
  split;[exact CALLED_BUFFER|]. split;[exact READY|]. split;assumption.
Qed.
