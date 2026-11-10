(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful scalar caller owns its same fresh bounded native buffer. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayNativeMemory GatewayHeapMemory GatewayNoMemory GatewayScalarNullFailure GatewayValueEntry GatewayValueContext
  GatewayValueStack GatewayValueRegions GatewayScalarLength GatewayScalarContext GatewayScalarGuards GatewayScalarLimits
  GatewayScalarMalloc GatewayScalarAllocationCall GatewayScalarAllocationPath GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_scalar_buffer_ready {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object memory world :Prop:=
  @gateway_value_sized World native stable discipline scalar slots stream_block stream_offset initial readonly original size memory world /\
  gateway_heap_context native discipline heap_allocation None object(Int64.unsigned size+1)memory world /\
  object<>stream_block /\object<>gateway_value_tag_slot slots /\object<>gateway_value_size_slot slots /\
  (forall position,~readonly object position).

Lemma gateway_scalar_buffer_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots stream_block stream_offset initial readonly original size object :
  GatewayOperations.gateway_runtime_discipline backend(gateway_scalar_buffer_ready native stable discipline heap_allocation
    scalar slots stream_block stream_offset initial readonly original size object).
Proof.
  intros before world after next[SIZED[HEAP REST]]INTERFERENCE;split.
  - eapply gateway_value_sized_ambient;[exact runtime|exact SIZED|exact INTERFERENCE].
  - split;[eapply gateway_heap_context_ambient;[exact runtime|exact HEAP|exact INTERFERENCE]|exact REST].
Qed.

Theorem gateway_actual_scalar_buffer_context {World Event}(backend:gateway_backend World Event)
    python objects detached io native stable thread_errno heap_allocation
    (discipline:option Values.val->Memory.mem->World->Prop)
    (base_runtime:gateway_thread_runtime backend io native stable(gateway_python_discipline python objects detached)thread_errno)
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (allocations:gateway_native_memory_runtime backend io native stable discipline heap_allocation)
    (errors:gateway_no_memory_runtime backend python)
    scalar slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next :
  (forall memory current,discipline None memory current ->gateway_objects_ready(python current)(objects current)memory) ->
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  gateway_value_sized native stable discipline scalar slots stream_block stream_offset
    initial readonly original size before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  Int64.unsigned size<=gateway_scalar_maximum scalar /\
  exists object called_parameters prefix allocating suffix malloc_before malloc_world malloc_after malloc_next,
    events=prefix++allocating++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_stream=Some(gateway_value_stream arguments) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(External EF_malloc[Ctypesdefs.tulong](Ctypesdefs.tptr Ctypesdefs.tvoid)cc_default)
        [Vlong(Int64.repr(Int64.unsigned size+1))]Kstop malloc_before)malloc_world)allocating
      (gateway_live(Returnstate(Vptr object Ptrofs.zero)Kstop malloc_after)malloc_next) /\
    gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots
      stream_block stream_offset initial readonly original size object malloc_after malloc_next /\
    gateway_received_bytes io(stream_descriptor initial)allocating=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_value_scalar_malloc_cont slots called_parameters)malloc_after)malloc_next)
      suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros NORMAL STREAM STREAM_PARAMETER INPUT RUN NONNULL.
  destruct(gateway_actual_scalar_allocation_call backend io native stable _ thread_errno runtime
    scalar slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next
    STREAM STREAM_PARAMETER INPUT RUN NONNULL)
    as(MAXIMUM &REMAINING &AMOUNT &called_parameters &prefix &allocating &suffix &malloc_before &malloc_world &malloc_after &malloc_next &
      pointer &EVENTS &QUIET &CALLED_STREAM &PREFIX &READY &MALLOC_RUN &REST).
  destruct(gateway_actual_scalar_malloc backend(Clight.globalenv prog)io native stable _ thread_errno heap_allocation runtime allocations
    scalar slots stream_block stream_offset initial readonly original size malloc_before malloc_world allocating pointer malloc_after malloc_next
    AMOUNT READY MALLOC_RUN)
    as(pending &returned &called &called_world &changed &changed_world &observed &MALLOC_EVENTS &TO_OPERATION &CALLED &OPERATION &FINAL &EMPTY).
  destruct FINAL as[FINAL_SIZED[NULL|[object[POINTER[FRESH HEAP]]]]].
  - subst pointer;exfalso;apply NONNULL.
    exact(gateway_actual_null_scalar_allocation backend python objects detached io native stable thread_errno base_runtime errors
      slots called_parameters malloc_after malloc_next suffix value after next
      (NORMAL _ _(proj1(proj1(proj1(proj1 FINAL_SIZED)))))REST).
  - subst pointer.
    destruct(proj1(proj1 CALLED))as(CONTEXT &TAG &SIZE &TAG_OWN &SIZE_OWN &SLOT_REST).
    destruct CONTEXT as(SIDE &STREAM_NATIVE &READONLY_STABLE &RAW &FRAME).
    assert(STREAM_LIVE:Mem.valid_block called stream_block).
    { eapply Mem.perm_valid_block;apply(gateway_value_stream_owned _ _ _ _ _ RAW(Ptrofs.unsigned stream_offset));lia. }
    assert(TAG_LIVE:Mem.valid_block called(gateway_value_tag_slot slots))by(eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia).
    assert(SIZE_LIVE:Mem.valid_block called(gateway_value_size_slot slots))by(eapply Mem.perm_valid_block;apply(SIZE_OWN 0);lia).
    split;[exact MAXIMUM|].
    exists object,called_parameters,prefix,allocating,suffix,malloc_before,malloc_world,malloc_after,malloc_next.
    split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact CALLED_STREAM|]. split;[exact MALLOC_RUN|]. split.
    + split;[exact FINAL_SIZED|]. split;[exact HEAP|].
      split;[intro SAME;subst object;contradiction|].
      split;[intro SAME;subst object;contradiction|].
      split;[intro SAME;subst object;contradiction|].
      intros position READ;apply FRESH;eapply gateway_value_readonly_live;[exact RAW|exact READ].
    + split;[exact EMPTY|exact REST].
Qed.

Theorem gateway_actual_scalar_buffer {World Event}(backend:gateway_backend World Event)
    python objects detached io native stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io native stable(gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io native stable(gateway_python_discipline python objects detached)heap_allocation)
    (errors:gateway_no_memory_runtime backend python)
    scalar slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  gateway_value_sized native stable(gateway_python_discipline python objects detached)scalar slots stream_block stream_offset
    initial readonly original size before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  Int64.unsigned size<=gateway_scalar_maximum scalar /\
  exists object called_parameters prefix allocating suffix malloc_before malloc_world malloc_after malloc_next,
    events=prefix++allocating++suffix /\called_parameters!_stream=Some(gateway_value_stream arguments) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(External EF_malloc[Ctypesdefs.tulong](Ctypesdefs.tptr Ctypesdefs.tvoid)cc_default)
        [Vlong(Int64.repr(Int64.unsigned size+1))]Kstop malloc_before)malloc_world)allocating
      (gateway_live(Returnstate(Vptr object Ptrofs.zero)Kstop malloc_after)malloc_next) /\
    gateway_scalar_buffer_ready native stable(gateway_python_discipline python objects detached)heap_allocation scalar slots
      stream_block stream_offset initial readonly original size object malloc_after malloc_next /\
    gateway_received_bytes io(stream_descriptor initial)allocating=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_value_scalar_malloc_cont slots called_parameters)malloc_after)malloc_next)
      suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM STREAM_PARAMETER INPUT RUN NONNULL.
  destruct(gateway_actual_scalar_buffer_context backend python objects detached io native stable thread_errno heap_allocation
    (gateway_python_discipline python objects detached)runtime runtime allocations errors scalar slots arguments parameters stream_block stream_offset initial
    readonly original size before world events value after next ltac:(intros;assumption)STREAM STREAM_PARAMETER INPUT RUN NONNULL)
    as(MAXIMUM &object &called_parameters &prefix &allocating &suffix &malloc_before &malloc_world &malloc_after &malloc_next &
      EVENTS &QUIET &CALLED_STREAM &MALLOC_RUN &READY &EMPTY &REST).
  split;[exact MAXIMUM|].
  exists object,called_parameters,prefix,allocating,suffix,malloc_before,malloc_world,malloc_after,malloc_next.
  split;[exact EVENTS|]. split;[exact CALLED_STREAM|]. split;[exact MALLOC_RUN|]. split;[exact READY|]. split;assumption.
Qed.
