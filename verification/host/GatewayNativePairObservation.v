(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Socketpair copyout and endpoint leases describe one physical row. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewaySpawnABI GatewaySpawnResources
  GatewaySpawnRuntime GatewaySpawnDescriptors GatewayNativeImport GatewayNativeWords GatewayNativeRows
  GatewayNativeReferences GatewayNativeCallOperands GatewayNativeStreamObservation.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Definition gateway_native_pair_code := ND.LeanCage_Host_NativeCode_Operation_socketPair
  (gateway_native_int Int.one) (gateway_native_int (Int.repr 526337)) (gateway_native_int Int.zero).

(* This is a single syscall's copyout/FD representation. The actual source
   producer supplies both loaded words; receipt existence alone cannot choose
   their orientation. Other native references remain the full row's values. *)
Record gateway_native_pair_runtime {World Event} (backend : gateway_backend World Event)
    (resources : World -> gateway_resource_state) (ipc : nat -> Prop)
    (rows : World -> Event -> option (nat * ND.LeanCage_Host_NativeCode_CallRow)) : Prop := {
  gateway_native_pair_outputs : forall object offset before world after next event selected row
      (receipt : gateway_socketpair_receipt ipc (resources world) (resources next)),
    gateway_spawn_operation backend gateway_socketpair_api
      [Vint Int.one; Vint (Int.repr 526337); Vint Int.zero; Vptr object offset]
      before world (Vint Int.zero) after next event ->
    rows world event = Some (selected, row) ->
    Mem.load Mint32 after object (Ptrofs.unsigned offset) =
      Some (Vint (Int.repr (gateway_pair_left _ _ _ receipt))) ->
    Mem.load Mint32 after object (Ptrofs.unsigned offset + 4) =
      Some (Vint (Int.repr (gateway_pair_right _ _ _ receipt))) ->
    gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_socketPair
      (gateway_native_int (Int.repr (gateway_pair_left _ _ _ receipt)))
      (gateway_native_int (Int.repr (gateway_pair_right _ _ _ receipt))) /\
    gateway_native_lease_at (gateway_native_row_output row) (gateway_pair_left _ _ _ receipt)
      (gateway_socket_descriptor (gateway_pair_left_object _ _ _ receipt)
        (gateway_pair_left_description _ _ _ receipt)) /\
    gateway_native_lease_at (gateway_native_row_output row) (gateway_pair_right _ _ _ receipt)
      (gateway_socket_descriptor (gateway_pair_right_object _ _ _ receipt)
        (gateway_pair_right_description _ _ _ receipt))
}.

Theorem gateway_actual_socket_pair_native_row {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions attributes resources ipc rows
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_native_pair_runtime backend resources ipc rows)
    object offset before world after next event
    (receipt : gateway_socketpair_receipt ipc (resources world) (resources next)) :
  gateway_spawn_operation backend gateway_socketpair_api
    [Vint Int.one; Vint (Int.repr 526337); Vint Int.zero; Vptr object offset]
    before world (Vint Int.zero) after next event ->
  Mem.load Mint32 after object (Ptrofs.unsigned offset) =
    Some (Vint (Int.repr (gateway_pair_left _ _ _ receipt))) ->
  Mem.load Mint32 after object (Ptrofs.unsigned offset + 4) =
    Some (Vint (Int.repr (gateway_pair_right _ _ _ receipt))) ->
  exists selected row,
    rows world event = Some (selected, row) /\
    gateway_native_row_process row = Nat_of_nat (process world) /\
    gateway_native_row_operation row = gateway_native_pair_code /\
    (position world <= selected < position next)%nat /\
    gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_socketPair
      (gateway_native_int (Int.repr (gateway_pair_left _ _ _ receipt)))
      (gateway_native_int (Int.repr (gateway_pair_right _ _ _ receipt))) /\
    gateway_native_lease_at (gateway_native_row_output row) (gateway_pair_left _ _ _ receipt)
      (gateway_socket_descriptor (gateway_pair_left_object _ _ _ receipt)
        (gateway_pair_left_description _ _ _ receipt)) /\
    gateway_native_lease_at (gateway_native_row_output row) (gateway_pair_right _ _ _ receipt)
      (gateway_socket_descriptor (gateway_pair_right_object _ _ _ receipt)
        (gateway_pair_right_description _ _ _ receipt)).
Proof.
  intros OPERATION LEFT RIGHT.
  assert (ACTUAL : gateway_runtime_operation backend (gateway_spawn_signature gateway_socketpair_api)
    [Vint Int.one; Vint (Int.repr 526337); Vint Int.zero; Vptr object offset]
    before world (Vint Int.zero) after next event).
  { destruct OPERATION as [definition [DEFINITION CURRENT]].
    rewrite (actual_gateway_spawn_signatures gateway_socketpair_api) in DEFINITION.
    inversion DEFINITION; subst; exact CURRENT. }
  assert (INPUTS : gateway_native_operation_inputs builders genuine actions attributes before world
    (gateway_spawn_signature gateway_socketpair_api)
    [Vint Int.one; Vint (Int.repr 526337); Vint Int.zero; Vptr object offset] gateway_native_pair_code).
  { apply gateway_native_direct_inputs; apply gateway_native_socketpair_operands. }
  destruct (gateway_native_operation_row _ _ _ _ _ _ _ _ recording _ _ _ _ _ _ _ _ _ INPUTS ACTUAL)
    as (selected & row & ROW & PROCESS & CODE & ORDER).
  exists selected, row.
  destruct (gateway_native_pair_outputs _ _ _ _ observation object offset before world after next event selected row
    receipt OPERATION ROW LEFT RIGHT) as [PRODUCT [FIRST SECOND]].
  repeat first [assumption |split].
Qed.
