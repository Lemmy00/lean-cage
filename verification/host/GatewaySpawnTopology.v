(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: A later fresh pair cannot alias an earlier retained endpoint. *)
From Stdlib Require Import ZArith List.
From HostGateway Require Import GatewaySpawnDescriptors GatewaySpawnResources.
Open Scope Z_scope.

Lemma gateway_owned_object_born state fd entry :
  gateway_resource_valid state -> gateway_owned_descriptor state fd entry ->
  gateway_resource_objects state (gateway_resource_object (gateway_descriptor_object entry)) = true.
Proof.
  intros [_ VALID] [_ LIVE]; destruct (VALID _ _ LIVE) as [_ [BORN REST]]; exact BORN.
Qed.

Theorem gateway_later_pair_separate ipc before after fd entry (receipt : gateway_socketpair_receipt ipc before after) :
  gateway_resource_valid before -> gateway_owned_descriptor before fd entry ->
  gateway_resource_object (gateway_descriptor_object entry) <> gateway_pair_left_object _ _ _ receipt /\
  gateway_resource_object (gateway_descriptor_object entry) <> gateway_pair_right_object _ _ _ receipt.
Proof.
  intros VALID LIVE; pose proof (gateway_owned_object_born _ _ _ VALID LIVE) as BORN.
  split; intro SAME; rewrite SAME in BORN.
  - rewrite (gateway_pair_left_fresh _ _ _ receipt) in BORN; discriminate.
  - rewrite (gateway_pair_right_fresh _ _ _ receipt) in BORN; discriminate.
Qed.
