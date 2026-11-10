(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: A pair's kernel birth is bound to its actual
   pending C output pointer without waiting for SDK return/copyout. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnResources GatewaySpawnDescriptors GatewayNativeImport
  GatewayNativeRows GatewayNativeWords GatewayNativeReferences GatewayNativePairObservation GatewayNativeStreamObservation GatewayChannelCodeProducer
  GatewayChannelSourceScope GatewayChannelPairSource GatewayPairSource GatewaySpawnHistory.
Import ListNotations.
Local Close Scope lean_scope.
Module ND := GatewayNativeImport.

(* The two resource views are the actual kernel snapshots at this selected
   linearization, not arbitrary states chosen after the fact. The receipt is
   only one socketpair's birth/FD/OFD representation, with actual output order. *)
Record gateway_pending_pair_runtime {World} (process position : World -> nat) (ipc : nat -> Prop)
    (before_resources after_resources : World -> nat -> gateway_resource_state)
    (pending : list Values.val -> mem -> World -> World -> nat -> ND.LeanCage_Host_NativeCode_CallRow -> Prop) : Prop := {
  gateway_pending_pair_primitive : forall memory world object current selected row,
    pending (pair_socket_arguments object Ptrofs.zero) memory world current selected row ->
    exists receipt : gateway_socketpair_receipt ipc (before_resources current selected) (after_resources current selected),
      gateway_native_row_process row = Nat_of_nat (process world) /\
      gateway_native_row_operation row = gateway_native_pair_code /\
      (position world <= selected < position current)%nat /\
      gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_socketPair
        (gateway_native_int (Int.repr (gateway_pair_left _ _ _ receipt)))
        (gateway_native_int (Int.repr (gateway_pair_right _ _ _ receipt))) /\
      gateway_native_lease_at (gateway_native_row_output row) (gateway_pair_left _ _ _ receipt)
        (gateway_socket_descriptor (gateway_pair_left_object _ _ _ receipt) (gateway_pair_left_description _ _ _ receipt)) /\
      gateway_native_lease_at (gateway_native_row_output row) (gateway_pair_right _ _ _ receipt)
        (gateway_socket_descriptor (gateway_pair_right_object _ _ _ receipt) (gateway_pair_right_description _ _ _ receipt))
}.

Theorem gateway_channel_pair_row_while_pending {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions attributes rows ipc before_resources after_resources pending
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_pending_pair_runtime process position ipc before_resources after_resources pending)
    invocation kind initial_memory initial_world events memory world actual_arguments current selected row :
  gateway_channel_pending_pair backend process position invocation kind initial_memory initial_world events memory world actual_arguments ->
  pending actual_arguments memory world current selected row ->
  exists use,
    (position initial_world <= selected < position current)%nat /\
    ND.LeanCage_Host_ChannelCode_PairUse_invocation use = invocation /\
    gateway_channel_pair_kind_of use = gateway_channel_kind kind /\
    ND.LeanCage_Host_ChannelCode_PairUse_position use = Nat_of_nat selected /\
    ND.LeanCage_Host_ChannelCode_PairUse_row use = row /\ gateway_channel_pair_checked use.
Proof.
  intros [SOURCE] OBSERVED.
  destruct SOURCE as (entry_arguments & environment & temporaries & allocated & storage & continuation &
    ENTRY & INVOCATION & INPUTS & PREFIX).
  subst invocation actual_arguments.
  destruct (@gateway_pending_pair_primitive World process position ipc before_resources after_resources pending observation
    memory world (gateway_channel_output storage kind) current selected row OBSERVED)
    as (receipt & PROCESS & CODE & ORDER & PRODUCT & LEFT & RIGHT).
  destruct (gateway_native_run_actor backend process position builders genuine actions attributes rows recording
    (Clight.globalenv prog) _ _ _ PREFIX) as [SAME_PROCESS LATER].
  cbn [gateway_state_world] in SAME_PROCESS, LATER.
  rewrite SAME_PROCESS in PROCESS.
  exists (gateway_channel_pair_use _ _ _ storage (process initial_world) (position initial_world)
    kind selected row ipc (before_resources current selected) (after_resources current selected) receipt).
  split; [lia |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  constructor; apply gateway_channel_pair_use_consistent; try assumption; lia.
Qed.
