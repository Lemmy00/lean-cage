(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Received path NUL bytes cannot become a successful parser result. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayTempNull GatewayFailurePaths GatewayValueEntry
  GatewayScalarLength GatewayScalarTerminate GatewayScalarPathSource GatewayScalarPathGuard GatewayScalarBytesPath
  GatewaySourceSegments GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Lemma gateway_path_failed_temp_null slots parameters scanned memory :
  parameters!_value=Some Vnullptr ->
  gateway_temp_null_source _value(gateway_path_scan_failed_state slots parameters scanned memory).
Proof.
  intro NULL;left;split;[eexists;eexists;reflexivity|]. split.
  - unfold gateway_path_scan_failed_state;cbn;rewrite PTree.gso by discriminate;exact NULL.
  - split;[reflexivity|right;split;[reflexivity|]].
    left;split;[|reflexivity].
    right;split;[reflexivity|]. eexists;eexists;reflexivity.
Qed.

Theorem gateway_actual_nul_path_denied {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next
    earlier later:
  parameters!_value=Some Vnullptr ->bytes=earlier++Byte.zero::later ->
  gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly
    original size object bytes before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.repr(Z.of_nat(length earlier)))))
      (gateway_path_scan_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intros NULL BYTES INPUT RUN.
  pose proof(gateway_path_positive_scan_segment backend ge io native stable discipline thread_errno runtime heap_allocation slots parameters
    stream_block stream_offset initial readonly original size object bytes before earlier later BYTES)as SEGMENT.
  destruct(gateway_source_segment_cut backend ge _ _ _ _ SEGMENT before world events value after next INPUT RUN)
    as(prefix &suffix &memory &current &EVENTS &QUIET &PREFIX &READY &REST).
  eapply gateway_actual_temp_null;[apply gateway_path_failed_temp_null;exact NULL|exact REST].
Qed.
