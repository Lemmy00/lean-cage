(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The number helper retains the enclosing scalar buffer and
   the exact current source-reference scope at each actual construction boundary. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceThreads GatewayScalarConstructorCalls GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_numeric_context {World}python objects decimal_float detached stable heap_allocation ledger held
    scalar slots stream_block stream_offset initial readonly original size object bytes memory world:Prop:=
  @gateway_scalar_private_ready World python objects detached stable heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes memory world /\gateway_reference_scope python objects decimal_float ledger held world.

Theorem gateway_reference_numeric_ambient {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger held scalar slots stream_block stream_offset initial readonly original size object bytes:
  gateway_ambient_closed backend(gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger held
    scalar slots stream_block stream_offset initial readonly original size object bytes).
Proof.
  intros first current last following[READY HELD]INTERFERENCE;split.
  - eapply gateway_scalar_private_ambient;[exact runtime|exact READY|exact INTERFERENCE].
  - eapply gateway_reference_scope_thread_effect;[exact HELD|].
    eapply gateway_reference_thread_ambient;[exact references|eapply gateway_scalar_private_side;exact READY|exact INTERFERENCE].
Qed.
