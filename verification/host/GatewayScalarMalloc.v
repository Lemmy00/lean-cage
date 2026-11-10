(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual allocator mints the buffer consumed by scalar decoding. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNativeMemory GatewayHeapMemory GatewayScalarContext
  GatewayScalarFrames GatewayOperations GatewayReadonly GatewayObjectRuns GatewayPathEvents GatewayRuntime
  GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Definition gateway_scalar_malloc_state {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size pointer origin memory world :Prop:=
  @gateway_value_sized World native stable discipline scalar slots stream_block stream_offset initial readonly original size memory world /\
  (pointer=Vnullptr \/exists object,pointer=Vptr object Ptrofs.zero /\~Mem.valid_block origin object /\
    gateway_heap_context native discipline heap_allocation None object(Int64.unsigned size+1)memory world).

Lemma gateway_scalar_malloc_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots stream_block stream_offset initial readonly original size pointer origin :
  gateway_runtime_discipline backend(gateway_scalar_malloc_state native stable discipline heap_allocation scalar slots
    stream_block stream_offset initial readonly original size pointer origin).
Proof.
  intros before world after next[SIZED RESULT]INTERFERENCE;split.
  - eapply gateway_value_sized_ambient;[exact runtime|exact SIZED|exact INTERFERENCE].
  - destruct RESULT as[NULL|[object[POINTER[FRESH HEAP]]]];[left;exact NULL|right].
    exists object;split;[exact POINTER|]. split;[exact FRESH|].
    eapply gateway_heap_context_ambient;[exact runtime|exact HEAP|exact INTERFERENCE].
Qed.

Theorem gateway_actual_scalar_malloc {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (allocations:gateway_native_memory_runtime backend io native stable discipline heap_allocation)
    scalar slots stream_block stream_offset initial readonly original size before world events pointer after next :
  0<Int64.unsigned size+1<=Int64.max_unsigned ->
  gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(External EF_malloc[tulong](tptr tvoid)cc_default)
      [Vlong(Int64.repr(Int64.unsigned size+1))]Kstop before)world)events
    (gateway_live(Returnstate pointer Kstop after)next) ->
  exists prefix suffix called called_world changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\
    gateway_steps backend ge
      (gateway_live(Callstate(External EF_malloc[tulong](tptr tvoid)cc_default)
        [Vlong(Int64.repr(Int64.unsigned size+1))]Kstop before)world)prefix
      (gateway_live(Callstate(External EF_malloc[tulong](tptr tvoid)cc_default)
        [Vlong(Int64.repr(Int64.unsigned size+1))]Kstop called)called_world) /\
    gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size called called_world /\
    gateway_runtime_operation backend(External EF_malloc[tulong](tptr tvoid)cc_default)
      [Vlong(Int64.repr(Int64.unsigned size+1))]called called_world pointer changed changed_world observed /\
    gateway_scalar_malloc_state native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
      size pointer called after next /\gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros AMOUNT INPUT RUN.
  set(sized:=gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size).
  pose proof(gateway_value_sized_ambient backend io native stable discipline thread_errno runtime
    scalar slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  pose proof(gateway_pending_run_ready backend ge sized CLOSED
    (Callstate(External EF_malloc[tulong](tptr tvoid)cc_default)[Vlong(Int64.repr(Int64.unsigned size+1))]Kstop before)
    before world prefix called called_world INPUT PENDING PREFIX)as CALLED.
  assert(API:gateway_memory_operation backend gateway_malloc_api[Vlong(Int64.repr(Int64.unsigned size+1))]
    called called_world pointer changed changed_world observed).
  { eexists;split;[exact(proj1 gateway_native_memory_actual_abis)|exact OPERATION]. }
  assert(SIDE:discipline None called called_world)by(exact(proj1(proj1(proj1(proj1 CALLED))))).
  destruct(gateway_malloc_operation _ _ _ _ _ _ allocations None called called_world(Int64.unsigned size+1)
    pointer changed changed_world observed SIDE AMOUNT API)as[NEXT[RETAINED[FRAME[NONIO RESULT]]]].
  assert(AFTER_SIZED:sized changed changed_world).
  { eapply gateway_value_sized_effect;[exact CALLED|exact NEXT|exact RETAINED|exact FRAME]. }
  set(ready:=gateway_scalar_malloc_state native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size pointer called).
  assert(AFTER:ready changed changed_world).
  { split;[exact AFTER_SIZED|]. destruct RESULT as[NULL|[receipt PRIVATE]];[left;exact NULL|right].
    exists(gateway_malloc_object _ _ _ _ _ receipt);split;[exact(gateway_malloc_pointer _ _ _ _ _ receipt)|].
    split;[exact(gateway_malloc_fresh _ _ _ _ _ receipt)|]. split;[exact NEXT|].
    split;[exact PRIVATE|]. split;[exact(gateway_malloc_origin _ _ _ _ _ receipt)|exact(gateway_malloc_live _ _ _ _ _ receipt)]. }
  pose proof(gateway_scalar_malloc_ambient backend io native stable discipline thread_errno runtime
    heap_allocation scalar slots stream_block stream_offset initial readonly original size pointer called)as READY_CLOSED.
  assert(FINAL:ready after next).
  { eapply(gateway_readonly_run_side backend ge ready READY_CLOSED(Returnstate pointer Kstop changed)changed_world
      suffix pointer after next);[exact I|exact AFTER|exact SUFFIX]. }
  assert(QUIET:Forall gateway_quiet_event suffix).
  { eapply(gateway_readonly_run_events backend ge(Returnstate pointer Kstop changed)changed_world
      suffix pointer after next);[exact I|exact SUFFIX]. }
  assert(EMPTY:gateway_received_bytes io(stream_descriptor initial)events=[]).
  { rewrite EVENTS,gateway_received_append,(gateway_pending_received_empty io(stream_descriptor initial)prefix PENDING).
    change(gateway_received_event io(stream_descriptor initial)(gateway_primitive observed)++
      gateway_received_bytes io(stream_descriptor initial)suffix=[]).
    unfold gateway_received_event;rewrite NONIO,(gateway_quiet_received io(stream_descriptor initial)suffix QUIET);reflexivity. }
  exists prefix,suffix,called,called_world,changed,changed_world,observed.
  split;[exact EVENTS|]. split;[exact PREFIX|]. split;[exact CALLED|]. split;[exact OPERATION|]. split;assumption.
Qed.
