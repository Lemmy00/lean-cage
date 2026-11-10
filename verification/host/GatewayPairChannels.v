(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Distinct peer births force distinct caller data/control descriptors. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers Values.
From HostGateway Require Import GatewaySpawnDescriptors GatewaySpawnResources GatewayPairContext
  GatewayConnectionResources GatewaySDKInputs GatewayExchangeFlagContext.
Open Scope Z_scope.

Theorem gateway_pair_channel_descriptors_separate ipc state(data control:gateway_pair_identity ipc)
    data_left data_right control_left control_right:
  gateway_pair_leases ipc data data_left data_right state->
  gateway_pair_leases ipc control control_left control_right state->
  pair_right_object ipc data<>pair_right_object ipc control->
  data_left<>control_left /\Int.repr data_left<>Int.repr control_left.
Proof.
  intros DATA CONTROL PEERS.
  assert(SLOTS:data_left<>control_left).
  { intro SAME;subst control_left.
    pose proof(proj2(gateway_pair_lease_left _ _ _ _ _ DATA))as LEFT_DATA.
    pose proof(proj2(gateway_pair_lease_left _ _ _ _ _ CONTROL))as LEFT_CONTROL.
    assert(ENTRY:pair_left_entry ipc data=pair_left_entry ipc control)by congruence.
    pose proof(f_equal(fun descriptor:gateway_resource_descriptor=>
      gateway_resource_object(gateway_descriptor_object descriptor))ENTRY)as OBJECT.
    change(pair_left_object ipc data=pair_left_object ipc control)in OBJECT.
    pose proof(gateway_pair_lease_left_peer _ _ _ _ _ DATA)as DATA_PEER.
    pose proof(gateway_pair_lease_left_peer _ _ _ _ _ CONTROL)as CONTROL_PEER.
    rewrite OBJECT in DATA_PEER;apply PEERS;congruence. }
  split;[exact SLOTS|].
  intro SAME;apply SLOTS.
  apply(f_equal Int.signed)in SAME.
  rewrite !Int.signed_repr in SAME;[exact SAME| |].
  all:pose proof(gateway_pair_lease_left_width _ _ _ _ _ DATA);
    pose proof(gateway_pair_lease_left_width _ _ _ _ _ CONTROL);
    change Int.min_signed with(-2147483648);lia.
Qed.

Theorem gateway_sdk_channel_descriptors_separate {World}native stable discipline resources ipc
    readonly selected reference owner original data_identity control_identity data control
    data_left data_right control_left control_right builders genuine actions attributes memory(world:World):
  gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original
    data_identity control_identity data control data_left data_right control_left control_right
    builders genuine actions attributes memory world->
  pair_right_object ipc data_identity<>pair_right_object ipc control_identity->
  Int.repr data_left<>Int.repr control_left.
Proof.
  intros[FLAGS REST]SEPARATE.
  destruct FLAGS as(SIDE & FAMILY & VALID & DATA & CONTROL & MODES & CELLS).
  exact(proj2(gateway_pair_channel_descriptors_separate ipc(resources world)data_identity control_identity
    data_left data_right control_left control_right DATA CONTROL SEPARATE)).
Qed.
