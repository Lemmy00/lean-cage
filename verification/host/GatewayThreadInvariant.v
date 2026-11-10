(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Per-operation invariants extend the same actual thread runtime. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayNativeMemory
  GatewayObjectThreads.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section ThreadInvariant.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (base:option Values.val->mem->World->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop).

Record gateway_thread_invariant_contract(property:World->Prop):Prop:={
  gateway_thread_invariant_ambient:forall mode before world after next,
    base mode before world->property world->gateway_interference backend before world after next->property next;
  gateway_thread_invariant_return:forall mode before world after_mode after next,
    property world->gateway_object_thread_operation backend native_private stable_readonly base heap_allocation
      mode before world after_mode after next->property next
}.

Definition gateway_thread_invariant_discipline(property:World->Prop)mode memory world:Prop:=
  base mode memory world /\property world.

Theorem gateway_thread_with_invariant property
    (runtime:gateway_thread_runtime backend io native_private stable_readonly base thread_errno)
    (contract:gateway_thread_invariant_contract property) :
  gateway_thread_runtime backend io native_private stable_readonly(gateway_thread_invariant_discipline property)thread_errno.
Proof.
  constructor.
  - intros mode before world after next[SIDE HELD]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
      as[NEXT OTHERS]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_ambient;[exact contract|exact SIDE|exact HELD|exact INTERFERENCE].
  - intros mode before world object[SIDE HELD]FRESH.
    eapply gateway_thread_fresh_native;[exact runtime|exact SIDE|exact FRESH].
  - intros mode before world object position[SIDE HELD]NATIVE.
    eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact NATIVE].
  - intros mode before world after object low high[SIDE HELD]ALLOC;split;[|exact HELD].
    eapply gateway_thread_native_alloc;[exact runtime|exact SIDE|exact ALLOC].
  - intros mode before world after object low high[SIDE HELD]NATIVE FREE;split;[|exact HELD].
    eapply gateway_thread_native_free;[exact runtime|exact SIDE|exact NATIVE|exact FREE].
  - intros mode before world after object offset chunk value[SIDE HELD]NATIVE STORE;split;[|exact HELD].
    eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact NATIVE|exact STORE].
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_save_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as[POINTER[NEXT OTHERS]]. split;[exact POINTER|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_save;eassumption.
  - intros saved before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as[NEXT OTHERS]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_restore;eassumption.
  - intros mode before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as(object &offset &RESULT &POINTER &LOAD &NATIVE &STABLE &NEXT &OTHERS).
    exists object,offset;split;[exact RESULT|]. split;[exact POINTER|]. split;[exact LOAD|].
    split;[exact NATIVE|]. split;[exact STABLE|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_errno;eassumption.
  - intros before world object offset result after next observed[SIDE HELD]NATIVE POINTER OPERATION.
    destruct(gateway_clock_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE NATIVE POINTER OPERATION)
      as(status &RESULT &CONTENT &NEXT &OTHERS).
    exists status;split;[exact RESULT|]. split;[exact CONTENT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_clock;eassumption.
  - intros saved before world object offset result after next observed[SIDE HELD]NATIVE POINTER OPERATION.
    destruct(gateway_poll_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE NATIVE POINTER OPERATION)
      as(status &RESULT &NEXT &OTHERS).
    exists status;split;[exact RESULT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_poll;eassumption.
  - intros mode before world descriptor object offset amount result after next observed
      [SIDE HELD]READABLE AMOUNT POINTER OPERATION.
    destruct(gateway_send_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE READABLE AMOUNT POINTER OPERATION)as(count &bytes &RANGE &RESULT &COUNT &LOAD &EVENT &NEXT &OTHERS).
    exists count,bytes;split;[exact RANGE|]. split;[exact RESULT|]. split;[exact COUNT|]. split;[exact LOAD|].
    split;[exact EVENT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_send;eassumption.
  - intros saved before world descriptor object offset amount result after next observed
      [SIDE HELD]NATIVE AMOUNT POINTER OPERATION.
    destruct(gateway_receive_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE NATIVE AMOUNT POINTER OPERATION)as(count &bytes &RANGE &RESULT &COUNT &LOAD &EVENT &NEXT &OTHERS).
    exists count,bytes;split;[exact RANGE|]. split;[exact RESULT|]. split;[exact COUNT|]. split;[exact LOAD|].
    split;[exact EVENT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_receive;eassumption.
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_check_signals_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as(status &RESULT &SUCCESS &EVENT).
    exists status;split;[exact RESULT|]. split;[|exact EVENT]. intros ZERO;subst status.
    destruct(SUCCESS eq_refl)as[NEXT OTHERS]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_signals;[exact SIDE|rewrite<-RESULT;exact OPERATION].
  - intros mode before world pointer result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_volatile_int_load _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE OPERATION)
      as[RESULT[NEXT OTHERS]]. split;[exact RESULT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_volatile;eassumption.
Qed.

Theorem gateway_memory_with_invariant property
    (runtime:gateway_native_memory_runtime backend io native_private stable_readonly base heap_allocation)
    (contract:gateway_thread_invariant_contract property) :
  gateway_native_memory_runtime backend io native_private stable_readonly(gateway_thread_invariant_discipline property)heap_allocation.
Proof.
  constructor.
  - intros mode before world amount result after next observed[SIDE HELD]AMOUNT OPERATION.
    destruct(gateway_malloc_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE AMOUNT OPERATION)
      as[NEXT OTHERS]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_malloc;eassumption.
  - intros mode before world object amount result after next observed[SIDE HELD]NATIVE AUTHORITY BLOCK OPERATION.
    destruct(gateway_free_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE NATIVE AUTHORITY BLOCK OPERATION)
      as[RESULT[NEXT OTHERS]]. split;[exact RESULT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_free;eassumption.
  - intros mode before world object offset amount bytes result after next observed
      [SIDE HELD]READABLE POINTER LOAD OPERATION.
    destruct(gateway_memchr_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE READABLE POINTER LOAD OPERATION)as[RESULT[NEXT OTHERS]].
    split;[exact RESULT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_thread_invariant_return;[exact contract|exact HELD|].
    eapply gateway_object_thread_memchr;eassumption.
Qed.

End ThreadInvariant.
