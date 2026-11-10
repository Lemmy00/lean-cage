(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same scalar caller proves its bounds before its actual allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayScalarLength
  GatewayScalarContext GatewayScalarGuards GatewayScalarLimits GatewayScalarAllocationPath GatewayMemoryBindings GatewayBindings
  GatewayNativeMemory GatewaySourcePaths GatewayFramedRuntime GatewayStreamInterface GatewayStreamLayout GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_scalar_allocation_call {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    scalar slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  Int64.unsigned size<=gateway_scalar_maximum scalar /\
  Int64.unsigned size<=Int64.unsigned(stream_remaining initial) /\
  0<Int64.unsigned size+1<=Int64.max_unsigned /\
  exists called_parameters prefix allocating suffix malloc_before malloc_world malloc_after malloc_next pointer,
    events=prefix++allocating++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_stream=Some(gateway_value_stream arguments) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)before)world)prefix
      (gateway_live(Callstate(External EF_malloc[tulong](tptr tvoid)cc_default)
        [Vlong(Int64.repr(Int64.unsigned size+1))](gateway_value_scalar_malloc_cont slots called_parameters)malloc_before)malloc_world) /\
    gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size
      malloc_before malloc_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(External EF_malloc[tulong](tptr tvoid)cc_default)
        [Vlong(Int64.repr(Int64.unsigned size+1))]Kstop malloc_before)malloc_world)allocating
      (gateway_live(Returnstate pointer Kstop malloc_after)malloc_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate pointer(gateway_value_scalar_malloc_cont slots called_parameters)malloc_after)malloc_next)
      suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM STREAM_PARAMETER INPUT RUN NONNULL.
  destruct actual_stream_layout as(_ & _ & _ & _ & _ &REMAINING_LAYOUT & _).
  destruct(gateway_actual_scalar_bounds backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    scalar slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next
    STREAM STREAM_PARAMETER REMAINING_LAYOUT INPUT RUN NONNULL)as[MAXIMUM_BOUND REMAINING_BOUND].
  assert(MAXIMUM:Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size=false).
  { unfold Int64.ltu;rewrite gateway_scalar_maximum_unsigned;destruct(zlt _ _);[lia|reflexivity]. }
  assert(REMAINING:Int64.ltu(stream_remaining initial)size=false).
  { unfold Int64.ltu;destruct(zlt _ _);[lia|reflexivity]. }
  destruct(gateway_actual_memory_binding gateway_malloc_api)as[definition[DEFINITION BINDING]].
  destruct gateway_native_memory_actual_abis as[MALLOC _].
  rewrite MALLOC in DEFINITION;inversion DEFINITION;subst definition.
  destruct BINDING as[symbol[SYMBOL FUNCTION]].
  destruct(gateway_scalar_allocation_path backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    scalar slots arguments parameters stream_block stream_offset initial readonly original size before symbol
    STREAM STREAM_PARAMETER REMAINING_LAYOUT SYMBOL FUNCTION MAXIMUM REMAINING)
    as(called_parameters &PATH &CALLED_STREAM).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &malloc_before &malloc_world &EVENTS &QUIET &PREFIX &READY &FROM_MALLOC).
  destruct(gateway_return_cut backend(Clight.globalenv prog)(External EF_malloc[tulong](tptr tvoid)cc_default)
    [Vlong(Int64.repr(Int64.unsigned size+1))](gateway_value_scalar_malloc_cont slots called_parameters)
    malloc_before malloc_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_MALLOC)
    as(allocating &suffix &pointer &malloc_after &malloc_next &REST_EVENTS &MALLOC_RUN &REST).
  split;[exact MAXIMUM_BOUND|]. split;[exact REMAINING_BOUND|].
  split;[exact(gateway_scalar_allocation_bound scalar size MAXIMUM_BOUND)|].
  exists called_parameters,prefix,allocating,suffix,malloc_before,malloc_world,malloc_after,malloc_next,pointer.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact CALLED_STREAM|].
  split;[exact PREFIX|]. split;[exact READY|]. split;assumption.
Qed.
