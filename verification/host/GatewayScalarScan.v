(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual native path scan observes the same received scalar bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNativeMemory GatewayScalarNativeEffects GatewayScalarTerminate
  GatewayScalarPayloadMemory GatewayScalarBuffer GatewayScalarContext GatewayOperations GatewayReadonly GatewayFramedRuntime
  GatewayStreamInterface GatewayThreadRuntime GatewayObjectRuns GatewayPathEvents.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_scalar_scan_pointer {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes memory world:
  @gateway_scalar_terminated_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object bytes memory world ->gateway_native_pointer memory object Ptrofs.zero(Int64.unsigned size)Readable.
Proof.
  intros[[[_[[_[PRIVATE[ORIGIN[BOUND[HEADER OWNED]]]]]SEPARATE]]PAYLOAD]TERMINATED].
  split;[pose proof(Int64.unsigned_range size);lia|]. split.
  - change(0+Int64.unsigned size<=18446744073709551616).
    change Int64.max_unsigned with 18446744073709551615 in BOUND;lia.
  - split;[eapply Mem.perm_valid_block;apply(OWNED(-8));lia|].
    intros position RANGE;eapply Mem.perm_implies;[apply OWNED;change(0<=position<Int64.unsigned size)in RANGE;lia|constructor].
Qed.

Theorem gateway_actual_scalar_scan {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (allocations:gateway_native_memory_runtime backend io native stable discipline heap_allocation)
    scalar slots stream_block stream_offset initial readonly original size object bytes
    before world events result after next descriptor:
  gateway_scalar_terminated_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object bytes before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(External(EF_external "memchr"(mksignature[Xptr;Xint;Xlong]Xptr cc_default))
      [tptr tvoid;tint;tulong](tptr tvoid)cc_default)[Vptr object Ptrofs.zero;Vint Int.zero;Vlong size]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->
  gateway_scalar_terminated_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object bytes after next /\gateway_memchr_result object Ptrofs.zero bytes result /\
    gateway_received_bytes io descriptor events=[].
Proof.
  intros INPUT RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  pose proof(gateway_scalar_terminated_ambient backend io native stable discipline thread_errno runtime heap_allocation scalar slots stream_block
    stream_offset initial readonly original size object bytes)as CLOSED.
  pose proof(gateway_pending_run_ready backend ge _ CLOSED
    (Callstate(External(EF_external "memchr"(mksignature[Xptr;Xint;Xlong]Xptr cc_default))
      [tptr tvoid;tint;tulong](tptr tvoid)cc_default)[Vptr object Ptrofs.zero;Vint Int.zero;Vlong size]Kstop before)
    before world prefix called called_world INPUT PENDING PREFIX)as CALLED.
  pose proof CALLED as[[[SIZED[[SIDE[PRIVATE[ORIGIN BLOCK]]]SEPARATE]][COUNT LOAD]]TERMINATED].
  assert(API:gateway_memory_operation backend gateway_memchr_api
    [Vptr object Ptrofs.zero;Vint Int.zero;Vlong(Int64.repr(Int64.unsigned size))]called called_world result changed changed_world observed).
  { rewrite Int64.repr_unsigned;eexists;split;[exact(proj2(proj2 gateway_native_memory_actual_abis))|exact OPERATION]. }
  destruct(gateway_memchr_operation _ _ _ _ _ _ allocations None called called_world object Ptrofs.zero(Int64.unsigned size)bytes result changed
    changed_world observed SIDE ltac:(left;exact PRIVATE)
    (gateway_scalar_scan_pointer native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original size object
      bytes called called_world CALLED)LOAD API)as[SCANNED[AFTER_SIDE[ACCESS[FRAME NONIO]]]].
  pose proof(gateway_scalar_terminated_native_effect native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object bytes called called_world changed changed_world CALLED AFTER_SIDE ACCESS FRAME)as AFTER.
  pose proof(gateway_readonly_run_side backend ge _ CLOSED(Returnstate result Kstop changed)changed_world suffix result after next I AFTER SUFFIX)as FINAL.
  split;[exact FINAL|]. split;[exact SCANNED|].
  rewrite EVENTS,gateway_received_append,(gateway_pending_received_empty io descriptor prefix PENDING).
  change(gateway_received_event io descriptor(gateway_primitive observed)++gateway_received_bytes io descriptor suffix=[]).
  unfold gateway_received_event;rewrite NONIO.
  pose proof(gateway_readonly_run_events backend ge(Returnstate result Kstop changed)changed_world suffix result after next I SUFFIX)as QUIET.
  rewrite(gateway_quiet_received io descriptor suffix QUIET);reflexivity.
Qed.
