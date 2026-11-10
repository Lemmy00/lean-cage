(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Interpret only source-held leases in the actual full parent fork table. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayNativeImport GatewayNativeRows
  GatewaySpawnResources GatewaySpawnDescriptors.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Local Opaque Nat_of_nat Z.to_nat.
Module ND := GatewayNativeImport.

Definition gateway_native_row_input (row : ND.LeanCage_Host_NativeCode_CallRow) :=
  match row with ND.LeanCage_Host_NativeCode_CallRow_mk _ _ input _ _ _ _ => input end.
Definition gateway_native_row_output (row : ND.LeanCage_Host_NativeCode_CallRow) :=
  match row with ND.LeanCage_Host_NativeCode_CallRow_mk _ _ _ output _ _ _ => output end.
Definition gateway_native_reference_handles (references : ND.LeanCage_Host_NativeCode_References) :=
  match references with ND.LeanCage_Host_NativeCode_References_mk handles _ _ => handles end.
Definition gateway_native_reference_cloexec (references : ND.LeanCage_Host_NativeCode_References) :=
  match references with ND.LeanCage_Host_NativeCode_References_mk _ cloexec _ => cloexec end.
Definition gateway_native_reference_directory (references : ND.LeanCage_Host_NativeCode_References) :=
  match references with ND.LeanCage_Host_NativeCode_References_mk _ _ directory => directory end.

Definition gateway_native_handle_identity (entry : gateway_resource_descriptor)
    (handle : ND.LeanCage_Host_NativeCode_Handle) : Prop :=
  match handle with ND.LeanCage_Host_NativeCode_Handle_mk object description _ _ =>
    object = Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry)) /\
    description = Nat_of_nat (gateway_resource_description (gateway_descriptor_object entry))
  end.

Definition gateway_native_lease_at (references : ND.LeanCage_Host_NativeCode_References)
    descriptor (entry : gateway_resource_descriptor) : Prop :=
  0 <= descriptor <= Int.max_signed /\ exists handle,
    gateway_native_reference_handles references (Nat_of_nat (Z.to_nat descriptor)) = ND.Option_some_inst1 _ handle /\
    gateway_native_handle_identity entry handle /\
    gateway_native_reference_cloexec references (Nat_of_nat (Z.to_nat descriptor)) =
      (if gateway_descriptor_cloexec entry then Bool_true else Bool_false).

Definition gateway_native_leased_references (state : gateway_resource_state)
    (references : ND.LeanCage_Host_NativeCode_References) : Prop :=
  forall descriptor entry, gateway_owned_descriptor state descriptor entry ->
    gateway_native_lease_at references descriptor entry.

(* This is the physical representation of the already held source leases at
   one SDK operation's selected kernel row. Other concurrent descriptor slots,
   full flags, SDK handles and CWD retain their actual row values. *)
Record gateway_native_reference_runtime {World Event} (backend : gateway_backend World Event)
    (resources : World -> gateway_resource_state)
    (rows : World -> Event -> option (nat * ND.LeanCage_Host_NativeCode_CallRow)) : Prop := {
  gateway_native_source_leases : forall definition arguments before world result after next observed selected row,
    gateway_runtime_operation backend definition arguments before world result after next observed ->
    rows world observed = Some (selected, row) ->
    gateway_native_leased_references (resources world) (gateway_native_row_input row)
}.

Theorem gateway_actual_row_leases {World Event} (backend : gateway_backend World Event) resources rows
    (runtime : gateway_native_reference_runtime backend resources rows)
    definition arguments before world result after next observed selected row leases :
  gateway_runtime_operation backend definition arguments before world result after next observed ->
  rows world observed = Some (selected, row) ->
  Forall (fun lease => gateway_owned_descriptor (resources world) (fst lease) (snd lease)) leases ->
  Forall (fun lease => gateway_native_lease_at (gateway_native_row_input row) (fst lease) (snd lease)) leases.
Proof.
  intros OPERATION ROW LEASES; eapply Forall_impl; [|exact LEASES].
  intros [descriptor entry] OWNED; cbn in *.
  eapply gateway_native_source_leases; [exact runtime |exact OPERATION |exact ROW |exact OWNED].
Qed.
