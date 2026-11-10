(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A number's Unicode operand is constructed from the same
   bounded owned bytes and minted at the selected actual UTF-8 SDK operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceNumericStorage GatewayReferenceNumericRequests
  GatewayScalarConstructorCalls GatewayScalarDecoding GatewayScalarLength GatewayScalarTerminate GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_numeric_text {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger owner held definition scalar slots stream_block stream_offset initial readonly original size object bytes mode_symbol
    before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_object_api_definition gateway_api_unicode_utf8=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->Int64.unsigned size<=65536->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall candidate position,gateway_scalar_mode_region mode_symbol candidate position->readonly candidate position)->
  gateway_steps backend ge(gateway_live(Callstate definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  exists characters final,
    gateway_utf8_text bytes characters /\
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
      size object bytes after next /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)result(gateway_unicode_object characters)])next.
Proof.
  intros FORMED VACANT SCOPE DEFINITION INPUT BOUND MODE SUBSET RUN NONNULL.
  destruct(gateway_actual_utf8_scalar_bytes backend ge python objects detached decimal_float io stable thread_errno runtime constructors
    definition heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes before world events result after next mode_symbol
    DEFINITION INPUT ltac:(lia)MODE SUBSET RUN NONNULL)as[characters TEXT].
  destruct(gateway_reference_actual_numeric_storage backend ge python objects detached io stable thread_errno heap_allocation decimal_float
    runtime constructors reference_threads ledger owner held gateway_api_unicode_utf8 definition
    [Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero](gateway_unicode_object characters)gateway_unicode_kind
    scalar slots stream_block stream_offset initial readonly original size object bytes before world events result after next
    FORMED VACANT SCOPE DEFINITION
    ltac:(intros memory current READY HELD;split;[|exact I];
      pose proof READY as[[[STORAGE[COUNT LOAD]]TERMINATED]PRIVATE];
      replace(Vlong size)with(Vlong(Int64.repr(Z.of_nat(length bytes))))by(rewrite COUNT,Int64.repr_unsigned;reflexivity);
      apply gateway_request_unicode_utf8;
      [eapply gateway_scalar_received_object;exact READY|exact TEXT|
       change Int64.max_signed with 9223372036854775807;lia|
       eapply gateway_scalar_current_mode;[exact READY|exact MODE|exact SUBSET]])
    eq_refl eq_refl ltac:(unfold gateway_destructor_kind;auto 9)INPUT RUN NONNULL)
    as(final &MINT &WELL &OWNED &READY &HELD).
  exists characters,final;exact(conj TEXT(conj MINT(conj WELL(conj OWNED(conj READY HELD))))).
Qed.
