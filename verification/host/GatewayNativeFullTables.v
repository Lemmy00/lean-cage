(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Full snapshot views retain every actual alias,
   including SDK support slots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayNativeImport GatewayNativeReferences GatewayNativeChannels GatewaySpawnResources
  GatewaySpawnDescriptors GatewaySpawnProcess GatewaySpawnPrivateAliases.
Local Close Scope lean_scope.
Open Scope Z_scope.
Local Opaque Nat_of_nat nat_of_Nat.
Module ND := GatewayNativeImport.

Definition gateway_native_full_table_view table references : Prop :=
  gateway_native_table_view table references /\
  forall descriptor handle,
    0 <= descriptor <= Int.max_signed ->
    gateway_native_reference_handles references (Nat_of_nat (Z.to_nat descriptor)) = ND.Option_some_inst1 _ handle ->
    exists entry, table descriptor = Some entry /\ gateway_native_handle_identity entry handle /\
      gateway_native_reference_cloexec references (Nat_of_nat (Z.to_nat descriptor)) =
        (if gateway_descriptor_cloexec entry then Bool_true else Bool_false).

Definition gateway_native_snapshot_table (references : ND.LeanCage_Host_NativeCode_References)
    : gateway_descriptor_table gateway_open_description :=
  fun descriptor => if Z_le_dec 0 descriptor then if Z_le_dec descriptor Int.max_signed then
    match gateway_native_reference_handles references (Nat_of_nat (Z.to_nat descriptor)) with
    | ND.Option_none_inst1 _ => None
    | ND.Option_some_inst1 _ (ND.LeanCage_Host_NativeCode_Handle_mk object description flags raw) =>
      Some {| gateway_descriptor_object :=
        {| gateway_resource_object := nat_of_Nat object; gateway_resource_description := nat_of_Nat description |};
        gateway_descriptor_cloexec :=
          match gateway_native_reference_cloexec references (Nat_of_nat (Z.to_nat descriptor)) with
          | Bool_true => true | Bool_false => false end |}
    end else None else None.

Theorem gateway_native_snapshot_complete references :
  gateway_native_full_table_view (gateway_native_snapshot_table references) references.
Proof.
  split.
  - intros descriptor entry BOUND FOUND.
    unfold gateway_native_snapshot_table in FOUND.
    destruct (Z_le_dec 0 descriptor); [|lia].
    destruct (Z_le_dec descriptor Int.max_signed); [|lia].
    destruct (gateway_native_reference_handles references (Nat_of_nat (Z.to_nat descriptor))) as [|handle] eqn:HANDLE;
      [discriminate |].
    destruct handle as [object description flags raw]; inversion FOUND; subst entry.
    split; [exact BOUND |]. eexists; split; [exact HANDLE |]. split.
    + change (object = Nat_of_nat (nat_of_Nat object) /\
        description = Nat_of_nat (nat_of_Nat description)).
      rewrite !Nat2natid; split; reflexivity.
    + cbn [gateway_descriptor_cloexec].
      destruct (gateway_native_reference_cloexec references (Nat_of_nat (Z.to_nat descriptor))); reflexivity.
  - intros descriptor handle BOUND HANDLE.
    destruct handle as [object description flags raw].
    eexists; split.
    + unfold gateway_native_snapshot_table.
      destruct (Z_le_dec 0 descriptor); [|lia].
      destruct (Z_le_dec descriptor Int.max_signed); [|lia].
      rewrite HANDLE; reflexivity.
    + split.
      * change (object = Nat_of_nat (nat_of_Nat object) /\
          description = Nat_of_nat (nat_of_Nat description)).
        rewrite !Nat2natid; split; reflexivity.
      * cbn [gateway_descriptor_cloexec].
        destruct (gateway_native_reference_cloexec references (Nat_of_nat (Z.to_nat descriptor))); reflexivity.
Qed.

Theorem gateway_native_full_table_absence table references object :
  gateway_native_full_table_view table references ->
  (forall descriptor entry, table descriptor = Some entry ->
    gateway_resource_object (gateway_descriptor_object entry) <> object) ->
  forall descriptor handle, 0 <= descriptor <= Int.max_signed ->
    gateway_native_reference_handles references (Nat_of_nat (Z.to_nat descriptor)) = ND.Option_some_inst1 _ handle ->
    ND.LeanCage_Host_NativeCode_Handle_object handle <> Nat_of_nat object.
Proof.
  intros [_ COMPLETE] ABSENT descriptor handle BOUND HANDLE.
  destruct (COMPLETE descriptor handle BOUND HANDLE) as (entry & PRESENT & IDENTITY & FLAG).
  destruct handle as [actual description flags raw].
  cbn [gateway_native_handle_identity] in IDENTITY.
  destruct IDENTITY as [IDENTITY DESCRIPTION]; subst actual.
  change (Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry)) <> Nat_of_nat object).
  intro SAME; apply (ABSENT descriptor entry PRESENT).
  apply (f_equal nat_of_Nat) in SAME; rewrite !nat2Natid in SAME; exact SAME.
Qed.

Theorem gateway_native_exec_full_table_excludes birth execution references data_peer control_peer data control object :
  gateway_exec_from_birth birth execution ->
  gateway_child_actions birth = gateway_private_spawn_plan data_peer control_peer ->
  4 <= data_peer -> 4 <= control_peer ->
  gateway_child_inherited birth data_peer = Some data -> gateway_child_inherited birth control_peer = Some control ->
  gateway_resource_object (gateway_descriptor_object data) <> object ->
  gateway_resource_object (gateway_descriptor_object control) <> object ->
  gateway_aliases_closeexec (fun endpoint => gateway_resource_object endpoint = object) (gateway_child_inherited birth) ->
  gateway_native_full_table_view (gateway_exec_descriptors execution) references ->
  forall descriptor handle, 0 <= descriptor <= Int.max_signed ->
    gateway_native_reference_handles references (Nat_of_nat (Z.to_nat descriptor)) = ND.Option_some_inst1 _ handle ->
    ND.LeanCage_Host_NativeCode_Handle_object handle <> Nat_of_nat object.
Proof.
  intros [_ [_ [_ [prepared [APPLIED EXEC]]]]] PLAN DATA_BOUND CONTROL_BOUND DATA CONTROL DATA_PUBLIC CONTROL_PUBLIC CLOSED FULL.
  eapply gateway_native_full_table_absence; [exact FULL |].
  intros descriptor entry FOUND.
  rewrite EXEC in FOUND.
  eapply gateway_private_spawn_closes_aliases with
    (protected := fun endpoint => gateway_resource_object endpoint = object)
    (table := gateway_child_inherited birth) (data_peer := data_peer) (cancel_peer := control_peer)
    (data_endpoint := data) (cancel_endpoint := control) (prepared := prepared); try eassumption.
  rewrite <- PLAN; exact APPLIED.
Qed.

Lemma gateway_native_lease_unique references descriptor first second :
  gateway_native_lease_at references descriptor first -> gateway_native_lease_at references descriptor second ->
  first = second.
Proof.
  intros [_ [left [LEFT [FIRST FIRST_FLAG]]]] [_ [right [RIGHT [SECOND SECOND_FLAG]]]].
  rewrite LEFT in RIGHT; inversion RIGHT; subst right.
  destruct left as [object description flags raw].
  destruct first as [[first_object first_description] first_flag].
  destruct second as [[second_object second_description] second_flag].
  cbn [gateway_native_handle_identity gateway_descriptor_object gateway_resource_object gateway_resource_description] in FIRST, SECOND.
  destruct FIRST as [FIRST_OBJECT FIRST_DESCRIPTION].
  destruct SECOND as [SECOND_OBJECT SECOND_DESCRIPTION].
  assert (OBJECT : first_object = second_object).
  { pose proof (eq_trans (eq_sym FIRST_OBJECT) SECOND_OBJECT) as SAME.
    apply (f_equal nat_of_Nat) in SAME; rewrite !nat2Natid in SAME; exact SAME. }
  assert (DESCRIPTION : first_description = second_description).
  { pose proof (eq_trans (eq_sym FIRST_DESCRIPTION) SECOND_DESCRIPTION) as SAME.
    apply (f_equal nat_of_Nat) in SAME; rewrite !nat2Natid in SAME; exact SAME. }
  subst second_object second_description.
  cbn [gateway_descriptor_cloexec] in FIRST_FLAG, SECOND_FLAG.
  destruct first_flag, second_flag; try congruence; reflexivity.
Qed.

Theorem gateway_native_full_table_source_lease table references descriptor entry :
  gateway_native_full_table_view table references -> gateway_native_lease_at references descriptor entry ->
  table descriptor = Some entry.
Proof.
  intros [_ COMPLETE] SOURCE.
  destruct SOURCE as [BOUND [handle [HANDLE [IDENTITY FLAG]]]].
  destruct (COMPLETE descriptor handle BOUND HANDLE) as (actual & FOUND & ACTUAL & ACTUAL_FLAG).
  assert (SAME : entry = actual).
  { eapply gateway_native_lease_unique with (references := references) (descriptor := descriptor).
    - split; [exact BOUND |]. exists handle; split; [exact HANDLE |]. split; assumption.
    - split; [exact BOUND |]. exists handle; split; [exact HANDLE |]. split; assumption. }
  rewrite SAME; exact FOUND.
Qed.
