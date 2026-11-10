(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Real C allocation lifetimes produce
   the shared invocation identity. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayChannelSourceScope GatewayNativeImport
  GatewaySpawnDescriptors GatewaySpawnResources GatewayNativeWords GatewayNativeRows GatewayNativeReferences GatewayNativeStreamObservation GatewayNativePairObservation GatewayPairNativeOrigin.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Lemma gateway_channel_nat_separate first second :
  first <> second -> ND.Ne Lean.Nat (Nat_of_nat first) (Nat_of_nat second).
Proof.
  revert second; induction first as [|first IH]; intros [|second] DIFFERENT;
    unfold ND.Ne, ND.Not; cbn [Nat_of_nat].
  - exfalso; apply DIFFERENT; reflexivity.
  - intro SAME; inversion SAME.
  - intro SAME; inversion SAME.
  - intro SAME; apply (IH second ltac:(lia)); inversion SAME; reflexivity.
Qed.

Definition gateway_channel_invocation environment before allocated
    (storage : gateway_channel_storage environment before allocated) process position :=
  ND.LeanCage_Host_ChannelCode_Invocation_mk
    (ND.LeanCage_Host_NativeCode_SourceKey_mk (Nat_of_nat process) (Nat_of_nat position)
      (Nat_of_nat (Pos.to_nat (gateway_channel_actions _ _ _ storage)))
      (Nat_of_nat (Pos.to_nat (gateway_channel_attributes _ _ _ storage))))
    (Nat_of_nat (Pos.to_nat (gateway_channel_data _ _ _ storage)))
    (Nat_of_nat (Pos.to_nat (gateway_channel_control _ _ _ storage))).

Lemma gateway_channel_invocation_formed environment before allocated
    (storage : gateway_channel_storage environment before allocated) process position :
  ND.LeanCage_Host_ChannelCode_Invocation_WellFormed
    (gateway_channel_invocation _ _ _ storage process position).
Proof.
  unfold ND.LeanCage_Host_ChannelCode_Invocation_WellFormed, gateway_channel_invocation.
  cbn.
  repeat apply Lean.And_intro.
  - apply gateway_channel_nat_separate; intro SAME; apply (gateway_channel_actions_attributes _ _ _ storage).
    apply Pos2Nat.inj; exact SAME.
  - apply gateway_channel_nat_separate; intro SAME; apply (gateway_channel_data_control _ _ _ storage).
    apply Pos2Nat.inj; exact SAME.
  - apply gateway_channel_nat_separate; intro SAME; apply (gateway_channel_data_actions _ _ _ storage).
    apply Pos2Nat.inj; exact SAME.
  - apply gateway_channel_nat_separate; intro SAME; apply (gateway_channel_data_attributes _ _ _ storage).
    apply Pos2Nat.inj; exact SAME.
  - apply gateway_channel_nat_separate; intro SAME; apply (gateway_channel_control_actions _ _ _ storage).
    apply Pos2Nat.inj; exact SAME.
  - apply gateway_channel_nat_separate; intro SAME; apply (gateway_channel_control_attributes _ _ _ storage).
    apply Pos2Nat.inj; exact SAME.
  - change (Lean.Nat_le (Nat_of_nat 1) (Nat_of_nat (Pos.to_nat (gateway_channel_actions _ _ _ storage)))).
    apply nat_le_Nat_le'; pose proof (Pos2Nat.is_pos (gateway_channel_actions _ _ _ storage)); lia.
  - change (Lean.Nat_le (Nat_of_nat 1) (Nat_of_nat (Pos.to_nat (gateway_channel_attributes _ _ _ storage)))).
    apply nat_le_Nat_le'; pose proof (Pos2Nat.is_pos (gateway_channel_attributes _ _ _ storage)); lia.
  - change (Lean.Nat_le (Nat_of_nat 1) (Nat_of_nat (Pos.to_nat (gateway_channel_data _ _ _ storage)))).
    apply nat_le_Nat_le'; pose proof (Pos2Nat.is_pos (gateway_channel_data _ _ _ storage)); lia.
  - change (Lean.Nat_le (Nat_of_nat 1) (Nat_of_nat (Pos.to_nat (gateway_channel_control _ _ _ storage)))).
    apply nat_le_Nat_le'; pose proof (Pos2Nat.is_pos (gateway_channel_control _ _ _ storage)); lia.
Qed.

Definition gateway_channel_kind kind :=
  match kind with
  | gateway_channel_data_pair => ND.LeanCage_Host_ChannelCode_PairKind_data
  | gateway_channel_control_pair => ND.LeanCage_Host_ChannelCode_PairKind_control
  end.

Lemma gateway_channel_storage_exact environment before allocated
    (storage : gateway_channel_storage environment before allocated) process position kind :
  ND.LeanCage_Host_ChannelCode_Invocation_storage
    (gateway_channel_invocation _ _ _ storage process position) (gateway_channel_kind kind) =
    Nat_of_nat (Pos.to_nat (gateway_channel_output storage kind)).
Proof. destruct kind; reflexivity. Qed.

Local Opaque Nat_of_nat Lean.double Z.to_nat.

Lemma gateway_channel_shared_double value :
  Z.of_nat (nat_of_Nat (Lean.double value)) = 2 * Z.of_nat (nat_of_Nat value).
Proof.
  induction value; cbn [Lean.double nat_of_Nat]; [reflexivity |].
  rewrite !Nat2Z.inj_succ, IHvalue; lia.
Qed.

Lemma gateway_channel_shared_succ value :
  Z.of_nat (nat_of_Nat (Lean.Nat_succ value)) = 1 + Z.of_nat (nat_of_Nat value).
Proof. cbn [nat_of_Nat]; rewrite Nat2Z.inj_succ; lia. Qed.

Fixpoint gateway_channel_positive (value : positive) : Lean.Nat :=
  match value with
  | xH => Lean.Nat_succ Lean.Nat_zero
  | xO rest => Lean.double (gateway_channel_positive rest)
  | xI rest => Lean.Nat_succ (Lean.double (gateway_channel_positive rest))
  end.

Lemma gateway_channel_positive_value value :
  Z.of_nat (nat_of_Nat (gateway_channel_positive value)) = Z.pos value.
Proof.
  induction value; cbn [gateway_channel_positive];
    repeat first [rewrite gateway_channel_shared_double |rewrite gateway_channel_shared_succ];
    rewrite ?IHvalue; cbn [nat_of_Nat]; lia.
Qed.

Lemma gateway_channel_positive_exact value :
  Nat_of_nat (Pos.to_nat value) = gateway_channel_positive value.
Proof.
  assert (SAME : nat_of_Nat (Nat_of_nat (Pos.to_nat value)) =
    nat_of_Nat (gateway_channel_positive value)).
  { apply Nat2Z.inj; rewrite nat2Natid, gateway_channel_positive_value; apply positive_nat_Z. }
  apply (f_equal Nat_of_nat) in SAME; rewrite !Nat2natid in SAME; exact SAME.
Qed.

Lemma gateway_channel_pair_bound descriptor :
  0 <= descriptor <= Int.max_signed ->
  ND.LE_le_inst1 Lean.Nat ND.instLENat (Nat_of_nat (Z.to_nat descriptor))
    (gateway_channel_positive 2147483647%positive).
Proof.
  intros BOUND; apply nat_le_Nat_le; apply Nat2Z.inj_le.
  rewrite nat2Natid, gateway_channel_positive_value, Z2Nat.id by lia.
  change Int.max_signed with 2147483647 in BOUND; lia.
Qed.

Lemma gateway_channel_lease_reference references descriptor entry :
  gateway_native_lease_at references descriptor entry ->
  ND.LeanCage_Host_ChannelCode_ReferenceAt references (Nat_of_nat (Z.to_nat descriptor))
    (Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry)))
    (Nat_of_nat (gateway_resource_description (gateway_descriptor_object entry))).
Proof.
  intros [BOUND [handle [HANDLE [IDENTITY FLAG]]]].
  destruct references as [handles cloexec cwd].
  cbn [gateway_native_reference_handles] in HANDLE.
  destruct handle as [object description flags raw].
  cbn [gateway_native_handle_identity] in IDENTITY.
  destruct IDENTITY as [OBJECT DESCRIPTION]; subst object description.
  unfold ND.LeanCage_Host_ChannelCode_ReferenceAt.
  refine (ND.Exists_intro _ _ (ND.LeanCage_Host_NativeCode_Handle_mk
    (Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry)))
    (Nat_of_nat (gateway_resource_description (gateway_descriptor_object entry))) flags raw) _).
  repeat apply Lean.And_intro.
  - change (Lean.eq (handles (Nat_of_nat (Z.to_nat descriptor)))
      (ND.Option_some_inst1 ND.LeanCage_Host_NativeCode_Handle
        (ND.LeanCage_Host_NativeCode_Handle_mk
          (Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry)))
          (Nat_of_nat (gateway_resource_description (gateway_descriptor_object entry))) flags raw))).
    rewrite HANDLE; constructor.
  - constructor.
  - constructor.
Qed.

Lemma gateway_channel_pair_code_exact :
  gateway_native_pair_code = ND.LeanCage_Host_NativeCode_Operation_socketPair
    (gateway_channel_positive 1%positive) (gateway_channel_positive 526337%positive) Lean.Nat_zero.
Proof.
  unfold gateway_native_pair_code.
  change (ND.LeanCage_Host_NativeCode_Operation_socketPair
    (gateway_native_int (Int.repr 1)) (gateway_native_int (Int.repr 526337))
    (gateway_native_int (Int.repr 0)) = ND.LeanCage_Host_NativeCode_Operation_socketPair
      (gateway_channel_positive 1%positive) (gateway_channel_positive 526337%positive) Lean.Nat_zero).
  rewrite !gateway_native_repr_int by (change Int.max_signed with 2147483647; lia).
  change (ND.LeanCage_Host_NativeCode_Operation_socketPair
    (Nat_of_nat (Pos.to_nat 1)) (Nat_of_nat (Pos.to_nat 526337)) (Nat_of_nat 0) =
      ND.LeanCage_Host_NativeCode_Operation_socketPair
      (gateway_channel_positive 1%positive) (gateway_channel_positive 526337%positive) Lean.Nat_zero).
  rewrite !gateway_channel_positive_exact; reflexivity.
Qed.

Definition gateway_channel_pair_use environment before allocated
    (storage : gateway_channel_storage environment before allocated) process position kind selected row
    ipc initial final (receipt : gateway_socketpair_receipt ipc initial final) :=
  ND.LeanCage_Host_ChannelCode_PairUse_mk
    (gateway_channel_invocation _ _ _ storage process position) (gateway_channel_kind kind) (Nat_of_nat selected) row
    (Nat_of_nat (Z.to_nat (gateway_pair_left _ _ _ receipt)))
    (Nat_of_nat (Z.to_nat (gateway_pair_right _ _ _ receipt)))
    (Nat_of_nat (gateway_pair_left_object _ _ _ receipt))
    (Nat_of_nat (gateway_pair_right_object _ _ _ receipt))
    (Nat_of_nat (gateway_pair_left_description _ _ _ receipt))
    (Nat_of_nat (gateway_pair_right_description _ _ _ receipt)).

Lemma gateway_channel_pair_use_consistent environment before allocated
    (storage : gateway_channel_storage environment before allocated) process position kind selected row
    ipc initial final (receipt : gateway_socketpair_receipt ipc initial final) :
  gateway_native_row_process row = Nat_of_nat process ->
  (position <= selected)%nat ->
  gateway_native_row_operation row = gateway_native_pair_code ->
  gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_socketPair
    (gateway_native_int (Int.repr (gateway_pair_left _ _ _ receipt)))
    (gateway_native_int (Int.repr (gateway_pair_right _ _ _ receipt))) ->
  gateway_native_lease_at (gateway_native_row_output row) (gateway_pair_left _ _ _ receipt)
    (gateway_socket_descriptor (gateway_pair_left_object _ _ _ receipt) (gateway_pair_left_description _ _ _ receipt)) ->
  gateway_native_lease_at (gateway_native_row_output row) (gateway_pair_right _ _ _ receipt)
    (gateway_socket_descriptor (gateway_pair_right_object _ _ _ receipt) (gateway_pair_right_description _ _ _ receipt)) ->
  ND.LeanCage_Host_ChannelCode_PairUse_Consistent
    (gateway_channel_pair_use _ _ _ storage process position kind selected row ipc initial final receipt).
Proof.
  intros PROCESS ORDER CODE PRODUCT LEFT RIGHT.
  pose proof (gateway_pair_left_width _ _ _ receipt) as LEFT_BOUND.
  pose proof (gateway_pair_right_width _ _ _ receipt) as RIGHT_BOUND.
  rewrite !gateway_native_repr_int in PRODUCT by assumption.
  unfold ND.LeanCage_Host_ChannelCode_PairUse_Consistent, gateway_channel_pair_use.
  cbn -[ND.LeanCage_Host_ChannelCode_Invocation_WellFormed gateway_channel_invocation Nat_of_nat Lean.double].
  apply Lean.And_intro; [apply gateway_channel_invocation_formed |].
  repeat apply Lean.And_intro.
  - change (Lean.eq (gateway_native_row_process row) (Nat_of_nat process)).
    rewrite PROCESS; constructor.
  - change (Lean.Nat_le (Nat_of_nat position) (Nat_of_nat selected)).
    apply nat_le_Nat_le'; exact ORDER.
  - change (Lean.eq (gateway_native_row_operation row)
      (ND.LeanCage_Host_NativeCode_Operation_socketPair
        (gateway_channel_positive 1%positive) (gateway_channel_positive 526337%positive) Lean.Nat_zero)).
    rewrite CODE, gateway_channel_pair_code_exact; constructor.
  - change (Lean.eq (gateway_native_row_product row)
      (ND.LeanCage_Host_NativeCode_Product_socketPair
        (Nat_of_nat (Z.to_nat (gateway_pair_left _ _ _ receipt)))
        (Nat_of_nat (Z.to_nat (gateway_pair_right _ _ _ receipt))))).
    rewrite PRODUCT; constructor.
  - apply gateway_channel_pair_bound; exact LEFT_BOUND.
  - apply gateway_channel_pair_bound; exact RIGHT_BOUND.
  - apply gateway_channel_nat_separate; intro SAME.
    apply (gateway_pair_slots_separate _ _ _ receipt), Z2Nat.inj; try lia.
  - apply gateway_channel_nat_separate; exact (gateway_pair_objects_separate _ _ _ receipt).
  - apply gateway_channel_nat_separate; exact (gateway_pair_descriptions_separate _ _ _ receipt).
  - exact (gateway_channel_lease_reference _ _ _ LEFT).
  - exact (gateway_channel_lease_reference _ _ _ RIGHT).
  - destruct LEFT as [_ [handle [_ [_ FLAG]]]].
    change (Lean.eq (gateway_native_reference_cloexec (gateway_native_row_output row)
      (Nat_of_nat (Z.to_nat (gateway_pair_left _ _ _ receipt)))) Bool_true).
    cbn [gateway_socket_descriptor gateway_descriptor_cloexec] in FLAG; rewrite FLAG; constructor.
  - destruct RIGHT as [_ [handle [_ [_ FLAG]]]].
    change (Lean.eq (gateway_native_reference_cloexec (gateway_native_row_output row)
      (Nat_of_nat (Z.to_nat (gateway_pair_right _ _ _ receipt)))) Bool_true).
    cbn [gateway_socket_descriptor gateway_descriptor_cloexec] in FLAG; rewrite FLAG; constructor.
Qed.

Record gateway_channel_pair_checked (use : ND.LeanCage_Host_ChannelCode_PairUse) : Prop := {
  gateway_channel_pair_consistent : ND.LeanCage_Host_ChannelCode_PairUse_Consistent use
}.

Definition gateway_channel_pair_kind_of (use : ND.LeanCage_Host_ChannelCode_PairUse) :=
  match use with ND.LeanCage_Host_ChannelCode_PairUse_mk _ kind _ _ _ _ _ _ _ _ => kind end.
