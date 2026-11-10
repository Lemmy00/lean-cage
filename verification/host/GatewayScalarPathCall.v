(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Path source cuts retain the same scan and decoder executions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayBindings GatewayNativeMemory GatewayMemoryBindings
  GatewayValueEntry GatewayScalarLength GatewayScalarReadPath GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarBytesPath
  GatewayScalarPathSource GatewayScalarCleanup GatewaySourcePaths GatewaySourceSegments GatewayObjects GatewayFramedRuntime
  GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Theorem actual_gateway_path_binding:
  exists definition,gateway_object_api_definition gateway_api_unicode_fs=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyUnicode_DecodeFSDefaultAndSize definition /\
    type_of_fundef definition=Tfunction[tptr tschar;tlong](tptr(Tstruct __object noattr))cc_default.
Proof.
  eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.

Theorem gateway_actual_path_scan_cut {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next:
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  gateway_scalar_payload_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly
    original size object bytes before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  exists called_parameters prefix scanning suffix scan_before scan_world scanned after_scan scan_next,
    events=prefix++scanning++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\called_parameters!_value=Some Vnullptr /\
    gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset initial
      readonly original size object bytes scan_before scan_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(External(EF_external "memchr"(mksignature[Xptr;Xint;Xlong]Xptr cc_default))
        [tptr tvoid;tint;tulong](tptr tvoid)cc_default)[Vptr object Ptrofs.zero;Vint Int.zero;Vlong size]Kstop scan_before)scan_world)scanning
      (gateway_live(Returnstate scanned Kstop after_scan)scan_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate scanned(gateway_path_scan_cont slots called_parameters)after_scan)scan_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros BUFFER INPUT RUN.
  destruct(gateway_actual_memory_binding gateway_memchr_api)as(definition &DEFINITION &[symbol[SYMBOL FUNCTION]]).
  pose proof(proj2(proj2 gateway_native_memory_actual_abis))as MEMCHR.
  rewrite MEMCHR in DEFINITION;inversion DEFINITION;subst definition.
  destruct(gateway_scalar_path_scan_source backend(Clight.globalenv prog)io native stable discipline thread_errno runtime heap_allocation slots parameters
    stream_block stream_offset initial readonly original size object bytes before symbol _ BUFFER SYMBOL FUNCTION eq_refl)
    as(called_parameters &SCAN_PATH &CALLED_BUFFER &CALLED_VALUE).
  pose proof(gateway_scalar_terminator_segment backend(Clight.globalenv prog)io native stable discipline thread_errno runtime heap_allocation
    gateway_scalar_path slots parameters stream_block stream_offset initial readonly original size object bytes before BUFFER)as TERMINATE.
  pose proof(gateway_segment_then_call backend(Clight.globalenv prog)_ _ _ _ _ _ _ _ TERMINATE SCAN_PATH)as PATH.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &scan_before &scan_world &EVENTS &QUIET &PREFIX &READY &FROM_SCAN).
  destruct(gateway_return_cut backend(Clight.globalenv prog)_ _ (gateway_path_scan_cont slots called_parameters)scan_before scan_world
    rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_SCAN)
    as(scanning &suffix &scanned &after_scan &scan_next &REST_EVENTS &SCAN &REST).
  exists called_parameters,prefix,scanning,suffix,scan_before,scan_world,scanned,after_scan,scan_next.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact CALLED_BUFFER|].
  split;[exact CALLED_VALUE|]. split;[exact READY|]. split;assumption.
Qed.

Theorem gateway_actual_path_constructor_cut {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next:
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly
    original size object bytes before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate Vnullptr(gateway_path_scan_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists definition called_parameters prefix constructing suffix constructor_before constructor_world constructor_after constructor_next,
    gateway_object_api_definition gateway_api_unicode_fs=Some definition /\events=prefix++constructing++suffix /\
    Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset initial
      readonly original size object bytes constructor_before constructor_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate definition[Vptr object Ptrofs.zero;Vlong size]Kstop constructor_before)constructor_world)constructing
      (gateway_live(Returnstate value Kstop constructor_after)constructor_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate value(gateway_scalar_constructor_cont _t'23 slots called_parameters)constructor_after)constructor_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros BUFFER INPUT RUN NONNULL.
  destruct actual_gateway_path_binding as(definition &DEFINITION &[symbol[SYMBOL FUNCTION]] &TYPE).
  destruct(gateway_scalar_path_decoder_source backend(Clight.globalenv prog)io native stable discipline thread_errno runtime heap_allocation slots parameters
    stream_block stream_offset initial readonly original size object bytes before symbol definition BUFFER SYMBOL FUNCTION TYPE)
    as(called_parameters &PATH &CALLED_BUFFER).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &constructor_before &constructor_world &EVENTS &QUIET &PREFIX &READY &FROM_CONSTRUCTOR).
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vptr object Ptrofs.zero;Vlong size]
    (gateway_scalar_constructor_cont _t'23 slots called_parameters)constructor_before constructor_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_CONSTRUCTOR)
    as(constructing &suffix &returned &constructor_after &constructor_next &REST_EVENTS &CONSTRUCTOR_RUN &REST).
  pose proof(proj1(gateway_actual_scalar_cleanup_cut backend _t'23 slots called_parameters object constructor_after constructor_next suffix returned value
    after next ltac:(discriminate)CALLED_BUFFER REST))as SAME;subst returned.
  exists definition,called_parameters,prefix,constructing,suffix,constructor_before,constructor_world,constructor_after,constructor_next.
  split;[exact DEFINITION|]. split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact CALLED_BUFFER|].
  split;[exact READY|]. split;assumption.
Qed.
