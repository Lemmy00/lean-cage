(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: A later pair retains the earlier pair's exact owned endpoints. *)
From Stdlib Require Import ZArith.
From HostGateway Require Import GatewaySpawnResources GatewaySpawnTopology GatewayPairContext GatewayPairHistory.

Theorem gateway_pair_resources_reference ipc(identity:gateway_pair_identity ipc)left right before after:
  gateway_pair_resources ipc identity left right before->gateway_resource_valid after->
  gateway_resource_reference before after->gateway_pair_resources ipc identity left right after.
Proof.
  intros[VALID[LEFT_BOUND[RIGHT_BOUND[SEPARATE[LEFT[RIGHT[LEFT_EX[RIGHT_EX[LEFT_NONBLOCK[RIGHT_NONBLOCK[
    LEFT_PEER[RIGHT_PEER[ORIGIN_VALID ORIGIN_REFERENCE]]]]]]]]]]]]]AFTER REFERENCE.
  destruct REFERENCE as[OWNED[OBJECTS[DESCRIPTIONS[PEERS[STATUS EXCLUSIVE]]]]].
  assert(LEFT_BORN:gateway_resource_objects before(pair_left_object _ identity)=true).
  { exact(gateway_owned_object_born before left(pair_left_entry ipc identity)VALID LEFT). }
  assert(RIGHT_BORN:gateway_resource_objects before(pair_right_object _ identity)=true).
  { exact(gateway_owned_object_born before right(pair_right_entry ipc identity)VALID RIGHT). }
  split;[exact AFTER|]. split;[exact LEFT_BOUND|]. split;[exact RIGHT_BOUND|]. split;[exact SEPARATE|].
  split;[apply OWNED;exact LEFT|]. split;[apply OWNED;exact RIGHT|].
  split;[apply EXCLUSIVE;exact LEFT_EX|]. split;[apply EXCLUSIVE;exact RIGHT_EX|]. split.
  - pose proof(STATUS left(pair_left_entry ipc identity)LEFT LEFT_EX ltac:(tauto))as SAME.
    change(gateway_resource_nonblocking after(pair_left_description _ identity)=
      gateway_resource_nonblocking before(pair_left_description _ identity))in SAME;rewrite SAME;exact LEFT_NONBLOCK.
  - split.
    + pose proof(STATUS right(pair_right_entry ipc identity)RIGHT RIGHT_EX ltac:(tauto))as SAME.
      change(gateway_resource_nonblocking after(pair_right_description _ identity)=
        gateway_resource_nonblocking before(pair_right_description _ identity))in SAME;rewrite SAME;exact RIGHT_NONBLOCK.
    + split;[apply PEERS;assumption|]. split;[apply PEERS;assumption|]. split;[exact ORIGIN_VALID|].
      eapply gateway_resource_reference_transitive;[exact ORIGIN_REFERENCE|].
      split;[exact OWNED|]. split;[exact OBJECTS|]. split;[exact DESCRIPTIONS|]. split;[exact PEERS|]. split;assumption.
Qed.
