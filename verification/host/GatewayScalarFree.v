(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual scalar cleanup releases only its same allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayScalarLength GatewayScalarContext GatewayScalarBuffer GatewayScalarPayloadMemory GatewayScalarSizedFrames
  GatewayNativeMemory GatewayHeapMemory GatewayOperations GatewayReadonly GatewayRuntime GatewayFramedRuntime
  GatewayObjectRuns GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_scalar_free_frame {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object before world after :
  @gateway_scalar_buffer_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object before world ->
  gateway_native_frame native stable(gateway_heap_region object(Int64.unsigned size+1))world before after ->
  Mem.unchanged_on(gateway_value_sized_region slots stream_block stream_offset readonly)before after.
Proof.
  intros[SIZED[HEAP[OBJECT_STREAM[OBJECT_TAG[OBJECT_SIZE AVOIDS]]]]]FRAME.
  destruct SIZED as[[[[SIDE[STREAM[STABLE[INPUT INITIAL_FRAME]]]][TAG[SIZE REST]]]TAG_LOAD]SIZE_LOAD].
  eapply Mem.unchanged_on_implies;[exact FRAME|].
  intros candidate position[[[SAME REGION]|READ]|[[SAME REGION]|[SAME REGION]]]LIVE;split.
  - subst candidate;left;exact STREAM.
  - intros[SAME_OBJECT RANGE];congruence.
  - right;apply STABLE;exact READ.
  - intros[SAME_OBJECT RANGE];subst candidate;exact(AVOIDS position READ).
  - subst candidate;left;exact TAG.
  - intros[SAME_OBJECT RANGE];congruence.
  - subst candidate;left;exact SIZE.
  - intros[SAME_OBJECT RANGE];congruence.
Qed.

Theorem gateway_actual_scalar_free {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (allocations:gateway_native_memory_runtime backend io native stable discipline heap_allocation)
    scalar slots stream_block stream_offset initial readonly original size object before world events returned after next :
  gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object before world ->
  gateway_steps backend ge(gateway_live(Callstate(External EF_free[tptr tvoid]tvoid cc_default)[Vptr object Ptrofs.zero]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  returned=Vundef /\gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros INPUT RUN.
  pose proof(gateway_scalar_buffer_ambient backend io native stable discipline thread_errno runtime heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object)as CLOSED.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  pose proof(gateway_pending_run_ready backend ge _ CLOSED
    (Callstate(External EF_free[tptr tvoid]tvoid cc_default)[Vptr object Ptrofs.zero]Kstop before)before world prefix called called_world
    INPUT PENDING PREFIX)as CALLED.
  destruct CALLED as[SIZED[HEAP SEPARATE]].
  destruct HEAP as[SIDE[PRIVATE[ORIGIN BLOCK]]].
  assert(API:gateway_memory_operation backend gateway_free_api[Vptr object Ptrofs.zero]called called_world returned changed changed_world observed).
  { eexists;split;[exact(proj1(proj2 gateway_native_memory_actual_abis))|exact OPERATION]. }
  destruct(gateway_free_operation _ _ _ _ _ _ allocations None called called_world object(Int64.unsigned size+1)returned changed changed_world observed
    SIDE PRIVATE ORIGIN BLOCK API)as[UNDEFINED[NEXT[RETAINED[FRAME[FREE[RELEASED NONIO]]]]]].
  assert(AFTER:gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size changed changed_world).
  { eapply gateway_value_sized_frame_effect;[exact SIZED|exact NEXT|exact RETAINED|].
    exact(gateway_scalar_free_frame native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original size object
      called called_world changed(conj SIZED(conj(conj SIDE(conj PRIVATE(conj ORIGIN BLOCK)))SEPARATE))FRAME). }
  pose proof(gateway_value_sized_ambient backend io native stable discipline thread_errno runtime
    scalar slots stream_block stream_offset initial readonly original size)as SIZED_CLOSED.
  pose proof(gateway_readonly_run_side backend ge _ SIZED_CLOSED(Returnstate returned Kstop changed)changed_world suffix returned after next
    I AFTER SUFFIX)as FINAL.
  assert(QUIET:Forall gateway_quiet_event suffix).
  { eapply(gateway_readonly_run_events backend ge(Returnstate returned Kstop changed)changed_world suffix returned after next);[exact I|exact SUFFIX]. }
  split;[exact UNDEFINED|]. split;[exact FINAL|].
  rewrite EVENTS,gateway_received_append,(gateway_pending_received_empty io(stream_descriptor initial)prefix PENDING).
  change(gateway_received_event io(stream_descriptor initial)(gateway_primitive observed)++
    gateway_received_bytes io(stream_descriptor initial)suffix=[]).
  unfold gateway_received_event;rewrite NONIO,(gateway_quiet_received io(stream_descriptor initial)suffix QUIET);reflexivity.
Qed.
