(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The complete actual native reader supplies permission retention
   and monotone source-reference counts from its same primitive/control history. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import AST Values Memory Integers Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceBalance GatewayThreadInvariant GatewayPermissionScopes GatewayPermissionEffects
  GatewayReadyActual GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_pool_lower_bound {World}(python:World->python_world)baseline current:Prop:=
  forall pointer,(python_native_strong(python baseline)pointer<=python_native_strong(python current)pointer)%nat.

Theorem gateway_reference_pool_thread_invariant {World Event}(backend:gateway_backend World Event)
    native stable base heap_allocation python objects
    (references:gateway_reference_thread_contract backend native stable base heap_allocation python objects)baseline:
  gateway_thread_invariant_contract backend native stable base heap_allocation(gateway_reference_pool_lower_bound python baseline).
Proof.
  constructor.
  - intros mode before world after next SIDE COUNTS INTERFERENCE.
    pose proof(gateway_reference_thread_ambient _ _ _ _ _ _ _ references mode before world after next SIDE INTERFERENCE)as EFFECT.
    intros pointer;specialize(COUNTS pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia.
  - intros mode before world after_mode after next COUNTS OPERATION.
    pose proof(gateway_reference_thread_return _ _ _ _ _ _ _ references mode before world after_mode after next OPERATION)as EFFECT.
    intros pointer;specialize(COUNTS pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia.
Qed.

Theorem gateway_actual_read_preserves_pool_and_permissions {World Event}(backend:gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects
    (runtime:gateway_thread_runtime backend io native stable base thread_errno)
    (references:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    before world stream_block stream_offset initial data_block data_offset amount readonly events after next:
  base None before world->native world stream_block->native world data_block->
  (forall object position,readonly object position->stable world object position)->
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_read)[Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount)]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  gateway_reference_pool_lower_bound python world next /\
  gateway_permission_frame(gateway_permission_region stream_block stream_offset readonly)before after /\
  exists bytes,gateway_read_receipt io before stream_block stream_offset initial data_block data_offset amount readonly events after bytes.
Proof.
  intros SIDE STREAM DATA STABLE INPUT RUN.
  pose proof(gateway_thread_with_invariant backend io native stable base thread_errno heap_allocation
    (gateway_reference_pool_lower_bound python world)runtime(gateway_reference_pool_thread_invariant backend native stable base heap_allocation python objects references world))as THREADS.
  assert(START:gateway_thread_invariant_discipline base(gateway_reference_pool_lower_bound python world)None before world)
    by(split;[exact SIDE|intros pointer;apply Nat.le_refl]).
  destruct(gateway_actual_complete_read backend io native stable _ thread_errno THREADS before world stream_block stream_offset initial data_block data_offset amount readonly
    events after next START STREAM DATA STABLE INPUT RUN)
    as(bytes &RECEIPT &[FINAL_SIDE COUNTS]&FINAL_STREAM &FINAL_DATA &FINAL_STABLE &NATIVE_RETAINED &STABLE_RETAINED).
  split;[exact COUNTS|]. split;[eapply gateway_permission_read_receipt;exact RECEIPT|]. exists bytes;exact RECEIPT.
Qed.
