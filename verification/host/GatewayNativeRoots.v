(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Outstanding native blocks retain their actual capabilities across calls. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayRuntimeABI.
Import ListNotations.

Definition gateway_native_roots {World}(native:World->block->Prop)(held:list block)memory world :Prop:=
  forall object,In object held->Mem.valid_block memory object /\native world object.

Lemma gateway_native_roots_effect {World}native stable held before world after next output :
  @gateway_native_roots World native held before world ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable output world before after ->
  gateway_native_roots native held after next.
Proof.
  intros ROOTS[RETAIN_NATIVE RETAIN_STABLE]FRAME object MEMBER;destruct(ROOTS object MEMBER)as[LIVE NATIVE].
  split;[eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply RETAIN_NATIVE;assumption].
Qed.

Section NativeRoots.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (base:option val->mem->World->Prop)(thread_errno:World->Integers.int).
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno).

Definition gateway_native_root_discipline held mode memory world :=
  base mode memory world /\gateway_native_roots native held memory world.

Theorem gateway_thread_with_native_roots held :
  gateway_thread_runtime backend io native stable(gateway_native_root_discipline held)thread_errno.
Proof.
  constructor.
  - intros mode before world after next[SIDE HELD]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
      as[NEXT[RETAINED FRAME]]. split;[|split;assumption]. split;[exact NEXT|].
    eapply gateway_native_roots_effect;eassumption.
  - intros mode before world object[SIDE HELD]FRESH.
    eapply gateway_thread_fresh_native;[exact runtime|exact SIDE|exact FRESH].
  - intros mode before world object position[SIDE HELD]NATIVE.
    eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact NATIVE].
  - intros mode before world after object low high[SIDE HELD]ALLOC;split.
    + eapply gateway_thread_native_alloc;[exact runtime|exact SIDE|exact ALLOC].
    + intros old MEMBER;destruct(HELD old MEMBER)as[LIVE NATIVE];split;[eapply Mem.valid_block_alloc;eassumption|exact NATIVE].
  - intros mode before world after object low high[SIDE HELD]NATIVE FREE;split.
    + eapply gateway_thread_native_free;[exact runtime|exact SIDE|exact NATIVE|exact FREE].
    + intros old MEMBER;destruct(HELD old MEMBER)as[LIVE PRIVATE];split;[eapply Mem.valid_block_free_1;eassumption|exact PRIVATE].
  - intros mode before world after object offset chunk value[SIDE HELD]NATIVE STORE;split.
    + eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact NATIVE|exact STORE].
    + intros old MEMBER;destruct(HELD old MEMBER)as[LIVE PRIVATE];split;[eapply Mem.store_valid_block_1;eassumption|exact PRIVATE].
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_save_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as[POINTER[NEXT[RETAINED[FRAME EVENT]]]].
    split;[exact POINTER|]. split;[|split;[exact RETAINED|split;assumption]]. split;[exact NEXT|].
    eapply gateway_native_roots_effect;eassumption.
  - intros saved before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as[NEXT[RETAINED[FRAME EVENT]]].
    split;[|split;[exact RETAINED|split;assumption]]. split;[exact NEXT|].
    eapply gateway_native_roots_effect;eassumption.
  - intros mode before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as(object &offset &RESULT &POINTER &LOAD &NATIVE &STABLE &NEXT &RETAINED &FRAME &EVENT).
    exists object,offset;split;[exact RESULT|]. split;[exact POINTER|]. split;[exact LOAD|].
    split;[exact NATIVE|]. split;[exact STABLE|]. split;[|split;[exact RETAINED|split;assumption]].
    split;[exact NEXT|];eapply gateway_native_roots_effect;eassumption.
  - intros before world object offset result after next observed[SIDE HELD]NATIVE POINTER OPERATION.
    destruct(gateway_clock_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE NATIVE POINTER OPERATION)
      as(status &RESULT &CONTENT &NEXT &RETAINED &PERMISSIONS &FRAME &EVENT).
    exists status;split;[exact RESULT|]. split;[exact CONTENT|].
    split;[|split;[exact RETAINED|split;[exact PERMISSIONS|split;assumption]]].
    split;[exact NEXT|];eapply gateway_native_roots_effect;eassumption.
  - intros saved before world object offset result after next observed[SIDE HELD]NATIVE POINTER OPERATION.
    destruct(gateway_poll_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE NATIVE POINTER OPERATION)
      as(status &RESULT &NEXT &RETAINED &PERMISSIONS &FRAME &EVENT).
    exists status;split;[exact RESULT|].
    split;[|split;[exact RETAINED|split;[exact PERMISSIONS|split;assumption]]].
    split;[exact NEXT|];eapply gateway_native_roots_effect;eassumption.
  - intros mode before world descriptor object offset amount result after next observed
      [SIDE HELD]READABLE AMOUNT POINTER OPERATION.
    destruct(gateway_send_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE READABLE AMOUNT POINTER OPERATION)as(count &bytes &RANGE &RESULT &COUNT &LOAD &EVENT &NEXT &RETAINED &FRAME).
    exists count,bytes;split;[exact RANGE|]. split;[exact RESULT|]. split;[exact COUNT|]. split;[exact LOAD|].
    split;[exact EVENT|]. split;[|split;assumption].
    split;[exact NEXT|];eapply gateway_native_roots_effect;eassumption.
  - intros saved before world descriptor object offset amount result after next observed
      [SIDE HELD]NATIVE AMOUNT POINTER OPERATION.
    destruct(gateway_receive_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE NATIVE AMOUNT POINTER OPERATION)as(count &bytes &RANGE &RESULT &COUNT &LOAD &EVENT &NEXT &RETAINED &PERMISSIONS &FRAME).
    exists count,bytes;split;[exact RANGE|]. split;[exact RESULT|]. split;[exact COUNT|]. split;[exact LOAD|].
    split;[exact EVENT|]. split;[|split;[exact RETAINED|split;assumption]].
    split;[exact NEXT|];eapply gateway_native_roots_effect;eassumption.
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_check_signals_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as(status &RESULT &SUCCESS &EVENT).
    exists status;split;[exact RESULT|]. split;[|exact EVENT]. intro ZERO.
    destruct(SUCCESS ZERO)as[NEXT[RETAINED FRAME]]. split;[|split;assumption].
    split;[exact NEXT|];eapply gateway_native_roots_effect;eassumption.
  - intros mode before world pointer result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_volatile_int_load _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE OPERATION)
      as[RESULT[NEXT[RETAINED[FRAME EVENT]]]].
    split;[exact RESULT|]. split;[|split;[exact RETAINED|split;assumption]].
    split;[exact NEXT|];eapply gateway_native_roots_effect;eassumption.
Qed.

End NativeRoots.
