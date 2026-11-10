(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: One held socket receive retains source-owned Python roots. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime GatewayStreamInterface
  GatewayPython GatewayObjects GatewayReferenceThreads GatewayReferenceLedger GatewayEOFNative GatewayThreadInvariant.
Import ListNotations.
Open Scope Z_scope.

(* Root accounting is the invocation-relative ledger, not public refcounts.
   The exact one-byte output must be genuinely native-private memory. *)
Record gateway_eof_reference_runtime {World Event}(backend:gateway_backend World Event)
    (native:World->block->Prop)(base:option Values.val->mem->World->Prop)
    (python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_eof_reference_operation:forall before world descriptor object offset result after next observed,
    base None before world->native world object->gateway_native_pointer before object offset 1 Writable->
    gateway_runtime_operation backend gateway_receive_definition
      [Vint descriptor;Vptr object offset;Vlong Int64.one;Vint Int.zero]before world result after next observed->
    gateway_reference_thread_effect python objects world next
}.

Theorem gateway_eof_with_reference_scope {World Event}(backend:gateway_backend World Event)io native stable base python objects
    (runtime:gateway_eof_receive_runtime backend io native stable base)
    (references:gateway_eof_reference_runtime backend native base python objects)
    decimal_float ledger held:
  gateway_eof_receive_runtime backend io native stable
    (gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
Proof.
  constructor;intros before world descriptor object offset result after next observed[SIDE HELD]PRIVATE POINTER OPERATION.
  destruct(gateway_eof_receive_operation _ _ _ _ _ runtime before world descriptor object offset result after next observed
    SIDE PRIVATE POINTER OPERATION)as(count&bytes&COUNT&VALUE&LENGTH&LOAD&IO&NORMAL&ACCESS&PERMISSIONS&FRAME).
  exists count,bytes;split;[exact COUNT|]. split;[exact VALUE|]. split;[exact LENGTH|]. split;[exact LOAD|].
  split;[exact IO|]. split.
  - split;[exact NORMAL|]. eapply gateway_reference_scope_thread_effect;[exact HELD|].
    eapply gateway_eof_reference_operation;[exact references|exact SIDE|exact PRIVATE|exact POINTER|exact OPERATION].
  - split;[exact ACCESS|]. split;assumption.
Qed.
