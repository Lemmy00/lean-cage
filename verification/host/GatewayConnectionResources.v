(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Endpoint identities persist when the engine-facing OFD becomes blocking. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers.
From HostGateway Require Import GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnTopology GatewayPairContext.
Open Scope Z_scope.

Record gateway_pair_leases ipc(identity:gateway_pair_identity ipc)left right(state:gateway_resource_state):Prop:={
  gateway_pair_lease_left_width:0<=left<=Int.max_signed;
  gateway_pair_lease_right_width:0<=right<=Int.max_signed;
  gateway_pair_lease_fds_separate:left<>right;
  gateway_pair_lease_left:gateway_owned_descriptor state left(pair_left_entry ipc identity);
  gateway_pair_lease_right:gateway_owned_descriptor state right(pair_right_entry ipc identity);
  gateway_pair_lease_left_exclusive:gateway_resource_exclusive state(pair_left_description _ identity)=true;
  gateway_pair_lease_right_exclusive:gateway_resource_exclusive state(pair_right_description _ identity)=true;
  gateway_pair_lease_left_peer:gateway_resource_peer state(pair_left_object _ identity)=Some(pair_right_object _ identity);
  gateway_pair_lease_right_peer:gateway_resource_peer state(pair_right_object _ identity)=Some(pair_left_object _ identity)
}.

Lemma gateway_pair_resources_leases ipc(identity:gateway_pair_identity ipc)left right state:
  gateway_pair_resources ipc identity left right state->gateway_pair_leases ipc identity left right state.
Proof.
  intros[VALID[LW[RW[SEPARATE[LEFT[RIGHT[LEX[REX[LNON[RNON[LPEER[RPEER REST]]]]]]]]]]]].
  constructor;assumption.
Qed.

Lemma gateway_pair_leases_frame ipc(identity:gateway_pair_identity ipc)left right before after:
  gateway_resource_valid before->gateway_pair_leases ipc identity left right before->
  gateway_resource_frame before after(fun _=>False)(fun _=>False)->gateway_exclusive_kept before after->
  gateway_pair_leases ipc identity left right after.
Proof.
  intros VALID[LW RW SEPARATE LEFT RIGHT LEX REX LPEER RPEER]FRAME EXCLUSIVE.
  assert(LEFT_BORN:gateway_resource_objects before(pair_left_object _ identity)=true).
  { exact(gateway_owned_object_born before left(pair_left_entry ipc identity)VALID LEFT). }
  assert(RIGHT_BORN:gateway_resource_objects before(pair_right_object _ identity)=true).
  { exact(gateway_owned_object_born before right(pair_right_entry ipc identity)VALID RIGHT). }
  constructor;try assumption.
  - eapply(proj1 FRAME);[exact LEFT|tauto].
  - eapply(proj1 FRAME);[exact RIGHT|tauto].
  - apply EXCLUSIVE;exact LEX.
  - apply EXCLUSIVE;exact REX.
  - destruct FRAME as[_[_[_[_ PEERS]]]];apply PEERS;assumption.
  - destruct FRAME as[_[_[_[_ PEERS]]]];apply PEERS;assumption.
Qed.

Definition gateway_pair_modes ipc(identity:gateway_pair_identity ipc)left_mode right_mode(state:gateway_resource_state):Prop:=
  gateway_resource_nonblocking state(pair_left_description _ identity)=left_mode /\
  gateway_resource_nonblocking state(pair_right_description _ identity)=right_mode.

Lemma gateway_pair_resources_modes ipc(identity:gateway_pair_identity ipc)left right state:
  gateway_pair_resources ipc identity left right state->gateway_pair_modes ipc identity true true state.
Proof. unfold gateway_pair_resources,gateway_pair_modes;tauto. Qed.

Lemma gateway_pair_modes_frame ipc(identity:gateway_pair_identity ipc)left right left_mode right_mode before after:
  gateway_pair_leases ipc identity left right before->gateway_pair_modes ipc identity left_mode right_mode before->
  gateway_resource_status_frame before after(fun _=>False)->gateway_pair_modes ipc identity left_mode right_mode after.
Proof.
  intros[LW RW SEPARATE LEFT RIGHT LEX REX LPEER RPEER][LNON RNON]STATUS;split.
  - pose proof(STATUS left(pair_left_entry ipc identity)LEFT LEX ltac:(tauto))as SAME.
    change(gateway_resource_nonblocking after(pair_left_description _ identity)=
      gateway_resource_nonblocking before(pair_left_description _ identity))in SAME;rewrite SAME;exact LNON.
  - pose proof(STATUS right(pair_right_entry ipc identity)RIGHT REX ltac:(tauto))as SAME.
    change(gateway_resource_nonblocking after(pair_right_description _ identity)=
      gateway_resource_nonblocking before(pair_right_description _ identity))in SAME;rewrite SAME;exact RNON.
Qed.

Lemma gateway_pair_engine_blocking ipc(identity:gateway_pair_identity ipc)left right before after:
  gateway_pair_leases ipc identity left right before->gateway_pair_modes ipc identity true true before->
  gateway_resource_status_frame before after(fun description=>description=pair_right_description _ identity)->
  gateway_resource_nonblocking after(pair_right_description _ identity)=false->
  gateway_pair_modes ipc identity true false after.
Proof.
  intros[LW RW SEPARATE LEFT RIGHT LEX REX LPEER RPEER][LNON RNON]STATUS BLOCKING;split;[|exact BLOCKING].
  pose proof(STATUS left(pair_left_entry ipc identity)LEFT LEX
    ltac:(exact(pair_descriptions_separate _ identity)))as SAME.
  change(gateway_resource_nonblocking after(pair_left_description _ identity)=
    gateway_resource_nonblocking before(pair_left_description _ identity))in SAME;rewrite SAME;exact LNON.
Qed.
