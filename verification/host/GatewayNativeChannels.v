(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual recorded file actions produce observations of the same full exec snapshot. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayNativeImport GatewayNativeReferences GatewaySpawnDescriptors GatewaySpawnResources
  GatewaySpawnProcess.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Lemma gateway_native_channel_nat_separate first second :
  first <> second -> ND.Ne Lean.Nat (Nat_of_nat first) (Nat_of_nat second).
Proof.
  revert second; induction first as [|first IH]; intros [|second] DIFFERENT;
    unfold ND.Ne, ND.Not; cbn [Nat_of_nat].
  - exfalso; apply DIFFERENT; reflexivity.
  - intro SAME; inversion SAME.
  - intro SAME; inversion SAME.
  - intro SAME; apply (IH second ltac:(lia)); inversion SAME; reflexivity.
Qed.

(* A descriptor representation at one physical observation. Other descriptors,
   open flags, SDK support handles and CWD remain in the actual complete row. *)
Definition gateway_native_table_view (table : gateway_descriptor_table gateway_open_description)
    (references : ND.LeanCage_Host_NativeCode_References) : Prop :=
  forall descriptor entry, 0 <= descriptor <= Int.max_signed -> table descriptor = Some entry ->
    gateway_native_lease_at references descriptor entry.

Lemma gateway_native_lease_object references descriptor entry :
  gateway_native_lease_at references descriptor entry ->
  ND.LeanCage_Host_NativeChannels_objectAt references (Nat_of_nat (Z.to_nat descriptor)) =
    ND.Option_some_inst1 _ (Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry))).
Proof.
  intros [BOUND [handle [HANDLE [IDENTITY FLAG]]]].
  destruct references as [handles cloexec directory].
  cbn [gateway_native_reference_handles] in HANDLE.
  change (ND.LeanCage_Host_NativeChannels_objectAt_match_1
    (fun _ => ND.Option_inst1 Lean.Nat) (handles (Nat_of_nat (Z.to_nat descriptor)))
    (fun _ => ND.Option_none_inst1 Lean.Nat)
    (fun selected => ND.Option_some_inst1 Lean.Nat (ND.LeanCage_Host_NativeCode_Handle_object selected)) =
    ND.Option_some_inst1 Lean.Nat (Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry)))).
  rewrite HANDLE.
  destruct handle as [object description flags raw]. cbn [gateway_native_handle_identity] in IDENTITY.
  destruct IDENTITY as [OBJECT DESCRIPTION]. subst object; reflexivity.
Qed.

Lemma gateway_native_lease_cloexec references descriptor entry :
  gateway_native_lease_at references descriptor entry ->
  ND.LeanCage_Host_NativeCode_References_closeOnExec references (Nat_of_nat (Z.to_nat descriptor)) =
    (if gateway_descriptor_cloexec entry then Bool_true else Bool_false).
Proof.
  intros [BOUND [handle [HANDLE [IDENTITY FLAG]]]].
  destruct references; exact FLAG.
Qed.

Theorem gateway_native_execution_channel_evidence birth execution data_fd control_fd data control references :
  gateway_exec_from_birth birth execution ->
  gateway_child_actions birth = gateway_private_spawn_plan data_fd control_fd ->
  4 <= data_fd -> 4 <= control_fd ->
  gateway_child_inherited birth data_fd = Some data -> gateway_child_inherited birth control_fd = Some control ->
  gateway_resource_object (gateway_descriptor_object data) <>
    gateway_resource_object (gateway_descriptor_object control) ->
  gateway_native_table_view (gateway_exec_descriptors execution) references ->
  ND.LeanCage_Host_NativeChannels_Evidence references
    (Nat_of_nat (gateway_resource_object (gateway_descriptor_object data)))
    (Nat_of_nat (gateway_resource_object (gateway_descriptor_object control))).
Proof.
  intros [_ [_ [_ [prepared [APPLIED EXEC]]]]] PLAN DATA_BOUND CONTROL_BOUND DATA CONTROL SEPARATE VIEW.
  rewrite PLAN in APPLIED.
  destruct (gateway_private_spawn_descriptors _ _ _ _ _ DATA_BOUND CONTROL_BOUND DATA CONTROL)
    as [expected [SAME [INPUT [OUTPUT [CANCELLATION CLOSED]]]]].
  rewrite APPLIED in SAME; inversion SAME; subst expected.
  assert (INPUT_VIEW : gateway_native_lease_at references 0
    {| gateway_descriptor_object := gateway_descriptor_object data; gateway_descriptor_cloexec := false |}).
  { apply VIEW; [change (0 <= 0 <= 2147483647); lia |rewrite EXEC; exact INPUT]. }
  assert (OUTPUT_VIEW : gateway_native_lease_at references 1
    {| gateway_descriptor_object := gateway_descriptor_object data; gateway_descriptor_cloexec := false |}).
  { apply VIEW; [change (0 <= 1 <= 2147483647); lia |rewrite EXEC; exact OUTPUT]. }
  assert (CONTROL_VIEW : gateway_native_lease_at references 3
    {| gateway_descriptor_object := gateway_descriptor_object control; gateway_descriptor_cloexec := false |}).
  { apply VIEW; [change (0 <= 3 <= 2147483647); lia |rewrite EXEC; exact CANCELLATION]. }
  pose proof (gateway_native_lease_object _ _ _ INPUT_VIEW) as INPUT_OBJECT.
  pose proof (gateway_native_lease_object _ _ _ OUTPUT_VIEW) as OUTPUT_OBJECT.
  pose proof (gateway_native_lease_object _ _ _ CONTROL_VIEW) as CONTROL_OBJECT.
  pose proof (gateway_native_lease_cloexec _ _ _ INPUT_VIEW) as INPUT_FLAG.
  pose proof (gateway_native_lease_cloexec _ _ _ OUTPUT_VIEW) as OUTPUT_FLAG.
  pose proof (gateway_native_lease_cloexec _ _ _ CONTROL_VIEW) as CONTROL_FLAG.
  cbn [gateway_descriptor_object gateway_descriptor_cloexec Z.to_nat] in
    INPUT_OBJECT, OUTPUT_OBJECT, CONTROL_OBJECT, INPUT_FLAG, OUTPUT_FLAG, CONTROL_FLAG.
  change (ND.LeanCage_Host_NativeChannels_objectAt references (Nat_of_nat 0) =
    ND.Option_some_inst1 Lean.Nat (Nat_of_nat (gateway_resource_object (gateway_descriptor_object data)))) in INPUT_OBJECT.
  change (ND.LeanCage_Host_NativeChannels_objectAt references (Nat_of_nat 1) =
    ND.Option_some_inst1 Lean.Nat (Nat_of_nat (gateway_resource_object (gateway_descriptor_object data)))) in OUTPUT_OBJECT.
  change (ND.LeanCage_Host_NativeChannels_objectAt references (Nat_of_nat 3) =
    ND.Option_some_inst1 Lean.Nat (Nat_of_nat (gateway_resource_object (gateway_descriptor_object control)))) in CONTROL_OBJECT.
  change (ND.LeanCage_Host_NativeCode_References_closeOnExec references (Nat_of_nat 0) = Bool_false) in INPUT_FLAG.
  change (ND.LeanCage_Host_NativeCode_References_closeOnExec references (Nat_of_nat 1) = Bool_false) in OUTPUT_FLAG.
  change (ND.LeanCage_Host_NativeCode_References_closeOnExec references (Nat_of_nat 3) = Bool_false) in CONTROL_FLAG.
  unfold ND.LeanCage_Host_NativeChannels_Evidence.
  repeat constructor.
  - change (Lean.eq (ND.LeanCage_Host_NativeChannels_objectAt references (Nat_of_nat 0))
      (ND.Option_some_inst1 Lean.Nat (Nat_of_nat (gateway_resource_object (gateway_descriptor_object data))))).
    rewrite INPUT_OBJECT; constructor.
  - change (Lean.eq (ND.LeanCage_Host_NativeChannels_objectAt references (Nat_of_nat 1))
      (ND.Option_some_inst1 Lean.Nat (Nat_of_nat (gateway_resource_object (gateway_descriptor_object data))))).
    rewrite OUTPUT_OBJECT; constructor.
  - change (Lean.eq (ND.LeanCage_Host_NativeChannels_objectAt references (Nat_of_nat 3))
      (ND.Option_some_inst1 Lean.Nat (Nat_of_nat (gateway_resource_object (gateway_descriptor_object control))))).
    rewrite CONTROL_OBJECT; constructor.
  - change (Lean.eq (ND.LeanCage_Host_NativeCode_References_closeOnExec references (Nat_of_nat 0)) Bool_false).
    rewrite INPUT_FLAG; constructor.
  - change (Lean.eq (ND.LeanCage_Host_NativeCode_References_closeOnExec references (Nat_of_nat 1)) Bool_false).
    rewrite OUTPUT_FLAG; constructor.
  - change (Lean.eq (ND.LeanCage_Host_NativeCode_References_closeOnExec references (Nat_of_nat 3)) Bool_false).
    rewrite CONTROL_FLAG; constructor.
  - apply gateway_native_channel_nat_separate; exact SEPARATE.
Qed.
