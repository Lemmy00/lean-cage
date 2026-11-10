(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Lift individual thread operations with a private SDK shadow. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayRuntimeABI GatewayRuntime
  GatewayBuilderHistory GatewaySpawnActions.
Import ListNotations.

Section BuilderThreads.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (base:option val->mem->World->Prop)(thread_errno:World->Integers.int).
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno).

Context(builders:World->gateway_spawn_builders)(actions attributes:block)
  (history:gateway_builder_history_runtime backend native builders actions attributes).
Hypothesis HEADERS:forall mode memory world,base mode memory world->
  gateway_builder_headers native actions attributes memory world.

Ltac retain_builder_shadow:=
  match goal with
  |SNAPSHOT:builders ?old = ?snapshot,
   SIDE:base ?mode ?before ?old,
   OPERATION:gateway_runtime_operation backend ?definition ?arguments ?before ?old ?returned ?after ?next ?observed
   |-builders ?next = ?snapshot=>
    rewrite(gateway_thread_observer_keeps_builders backend native builders actions attributes history
      definition arguments before old returned after next observed(HEADERS mode before old SIDE)
      ltac:(unfold gateway_thread_resource_observer;cbn;auto 10)OPERATION);exact SNAPSHOT
  |SNAPSHOT:builders ?old = ?snapshot,
   SIDE:base ?mode ?before ?old,
   OPERATION:gateway_builtin backend _ _ _ ?before ?old ?returned ?after ?next ?observed
   |-builders ?next = ?snapshot=>
    rewrite(gateway_builder_history_volatile _ _ _ _ _ history before old _ returned after next observed
      (HEADERS mode before old SIDE)OPERATION);exact SNAPSHOT
  |SNAPSHOT:builders ?old = ?snapshot,
   SIDE:base ?mode ?before ?old,
   INTERFERENCE:gateway_interference backend ?before ?old ?after ?next
   |-builders ?next = ?snapshot=>
    rewrite(gateway_builder_history_ambient _ _ _ _ _ history before old after next
      (HEADERS mode before old SIDE)INTERFERENCE);exact SNAPSHOT
  end.


Definition gateway_builder_thread_discipline snapshot mode memory world :=
  base mode memory world /\builders world=snapshot.

Theorem gateway_thread_with_builder_history snapshot :
  gateway_thread_runtime backend io native stable(gateway_builder_thread_discipline snapshot)thread_errno.
Proof.
  constructor.
  - intros mode before world after next[SIDE HELD]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
      as[NEXT[RETAINED FRAME]]. split;[|split;assumption]. split;[exact NEXT|].
    retain_builder_shadow.
  - intros mode before world object[SIDE HELD]FRESH.
    eapply gateway_thread_fresh_native;[exact runtime|exact SIDE|exact FRESH].
  - intros mode before world object position[SIDE HELD]NATIVE.
    eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact NATIVE].
  - intros mode before world after object low high[SIDE HELD]ALLOC;split.
    + eapply gateway_thread_native_alloc;[exact runtime|exact SIDE|exact ALLOC].
    + exact HELD.
  - intros mode before world after object low high[SIDE HELD]NATIVE FREE;split.
    + eapply gateway_thread_native_free;[exact runtime|exact SIDE|exact NATIVE|exact FREE].
    + exact HELD.
  - intros mode before world after object offset chunk value[SIDE HELD]NATIVE STORE;split.
    + eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact NATIVE|exact STORE].
    + exact HELD.
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_save_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as[POINTER[NEXT[RETAINED[FRAME EVENT]]]].
    split;[exact POINTER|]. split;[|split;[exact RETAINED|split;assumption]]. split;[exact NEXT|].
    retain_builder_shadow.
  - intros saved before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as[NEXT[RETAINED[FRAME EVENT]]].
    split;[|split;[exact RETAINED|split;assumption]]. split;[exact NEXT|].
    retain_builder_shadow.
  - intros mode before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as(object &offset &RESULT &POINTER &LOAD &NATIVE &STABLE &NEXT &RETAINED &FRAME &EVENT).
    exists object,offset;split;[exact RESULT|]. split;[exact POINTER|]. split;[exact LOAD|].
    split;[exact NATIVE|]. split;[exact STABLE|]. split;[|split;[exact RETAINED|split;assumption]].
    split;[exact NEXT|];retain_builder_shadow.
  - intros before world object offset result after next observed[SIDE HELD]NATIVE POINTER OPERATION.
    destruct(gateway_clock_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE NATIVE POINTER OPERATION)
      as(status &RESULT &CONTENT &NEXT &RETAINED &PERMISSIONS &FRAME &EVENT).
    exists status;split;[exact RESULT|]. split;[exact CONTENT|].
    split;[|split;[exact RETAINED|split;[exact PERMISSIONS|split;assumption]]].
    split;[exact NEXT|];retain_builder_shadow.
  - intros saved before world object offset result after next observed[SIDE HELD]NATIVE POINTER OPERATION.
    destruct(gateway_poll_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE NATIVE POINTER OPERATION)
      as(status &RESULT &NEXT &RETAINED &PERMISSIONS &FRAME &EVENT).
    exists status;split;[exact RESULT|].
    split;[|split;[exact RETAINED|split;[exact PERMISSIONS|split;assumption]]].
    split;[exact NEXT|];retain_builder_shadow.
  - intros mode before world descriptor object offset amount result after next observed
      [SIDE HELD]READABLE AMOUNT POINTER OPERATION.
    destruct(gateway_send_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE READABLE AMOUNT POINTER OPERATION)as(count &bytes &RANGE &RESULT &COUNT &LOAD &EVENT &NEXT &RETAINED &FRAME).
    exists count,bytes;split;[exact RANGE|]. split;[exact RESULT|]. split;[exact COUNT|]. split;[exact LOAD|].
    split;[exact EVENT|]. split;[|split;assumption].
    split;[exact NEXT|];retain_builder_shadow.
  - intros saved before world descriptor object offset amount result after next observed
      [SIDE HELD]NATIVE AMOUNT POINTER OPERATION.
    destruct(gateway_receive_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE NATIVE AMOUNT POINTER OPERATION)as(count &bytes &RANGE &RESULT &COUNT &LOAD &EVENT &NEXT &RETAINED &PERMISSIONS &FRAME).
    exists count,bytes;split;[exact RANGE|]. split;[exact RESULT|]. split;[exact COUNT|]. split;[exact LOAD|].
    split;[exact EVENT|]. split;[|split;[exact RETAINED|split;assumption]].
    split;[exact NEXT|];retain_builder_shadow.
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_check_signals_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as(status &RESULT &SUCCESS &EVENT).
    exists status;split;[exact RESULT|]. split;[|exact EVENT]. intro ZERO.
    destruct(SUCCESS ZERO)as[NEXT[RETAINED FRAME]]. split;[|split;assumption].
    split;[exact NEXT|];retain_builder_shadow.
  - intros mode before world pointer result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_volatile_int_load _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE OPERATION)
      as[RESULT[NEXT[RETAINED[FRAME EVENT]]]].
    split;[exact RESULT|]. split;[|split;[exact RETAINED|split;assumption]].
    split;[exact NEXT|];retain_builder_shadow.
Qed.

End BuilderThreads.
