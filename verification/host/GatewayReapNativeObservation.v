(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Wait status bytes and the physical row share one SDK event. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayReapRuntime GatewayReapNativeOperands GatewayNativeImport GatewayNativeRows GatewayExchangeABI.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Local Opaque Nat_of_nat.
Module ND := GatewayNativeImport.

Theorem gateway_actual_wait_native_observation {World Event}(backend:gateway_backend World Event)
    io observation native stable discipline thread_errno
    (runtime:gateway_reap_runtime backend io observation native stable discipline thread_errno)
    process position rows pending
    (row_runtime:gateway_native_reap_row_runtime backend process position rows pending)
    mode before world child options object offset result after next event:
  discipline mode before world->0<Int.signed child->(options=Int.zero\/options=Int.one)->native world object->
  gateway_native_pointer before object offset 4 Writable->
  gateway_runtime_operation backend gateway_waitpid_definition[Vint child;Vptr object offset;Vint options]
    before world result after next event->
  exists selected row observed status,
    rows world event=Some(selected,row) /\gateway_native_row_process row=Nat_of_nat(process world) /\
    gateway_native_row_operation row=gateway_native_wait_code child options /\(position world<=selected<position next)%nat /\
    result=Vint observed /\(observed=Int.neg Int.one\/(observed=Int.zero /\options=Int.one)\/observed=child) /\
    (observed=child->exists word,status=Some word /\Mem.loadv Mint32 after(Vptr object offset)=Some(Vint word) /\
      Mem.loadbytes after object(Ptrofs.unsigned offset)4=Some(encode_val Mint32(Vint word))) /\
    (observed<>child->status=None) /\
    observation event=Some(gateway_reap_wait child options observed status(gateway_reap_errno observed(thread_errno next))) /\
    discipline mode after next /\gateway_access_retained native stable before world next /\
    gateway_native_permissions before after object offset 4 /\
    gateway_native_frame native stable(gateway_native_region object offset 4)world before after /\io event=None.
Proof.
  intros SIDE CHILD OPTIONS PRIVATE POINTER OPERATION.
  destruct(gateway_actual_reap_native_row backend process position rows pending row_runtime
    gateway_waitpid_definition[Vint child;Vptr object offset;Vint options](gateway_native_wait_code child options)
    before world result after next event(gateway_native_wait_operands before child options object offset POINTER)OPERATION)
    as(selected&row&ROW&PROCESS&CODE&ORDER).
  destruct(gateway_reap_wait_operation _ _ _ _ _ _ _ runtime mode before world child options object offset
    result after next event SIDE CHILD OPTIONS PRIVATE POINTER OPERATION)
    as(observed&status&RESULT&RANGE&BYTES&ABSENT&OBSERVATION&AFTER&ACCESS&PERMISSIONS&FRAME&IO).
  exists selected,row,observed,status.
  split;[exact ROW|]. split;[exact PROCESS|]. split;[exact CODE|]. split;[exact ORDER|].
  repeat first[assumption|split].
Qed.

Theorem gateway_actual_pending_wait_native_observation {World Event}(backend:gateway_backend World Event)
    process position rows pending
    (runtime:gateway_native_reap_row_runtime backend process position rows pending)
    before entry current selected row child options object offset:
  gateway_native_pointer before object offset 4 Writable->
  pending gateway_waitpid_definition[Vint child;Vptr object offset;Vint options]before entry current selected row->
  gateway_native_row_process row=Nat_of_nat(process entry) /\
    gateway_native_row_operation row=gateway_native_wait_code child options /\
    (position entry<=selected<position current)%nat.
Proof.
  intros POINTER OBSERVED;eapply gateway_actual_pending_reap_native_row;
    [exact runtime|apply gateway_native_wait_operands;exact POINTER|exact OBSERVED].
Qed.
