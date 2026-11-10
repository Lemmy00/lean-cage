(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: A fresh pair preserves every older caller lease and its open-description state. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values.
From HostGateway Require Import GatewaySpawnDescriptors GatewaySpawnResources GatewaySpawnRuntime.

Definition gateway_resource_reference(origin current:gateway_resource_state):Prop:=
  (forall fd entry,gateway_owned_descriptor origin fd entry->gateway_owned_descriptor current fd entry) /\
  (forall object,gateway_resource_objects origin object=true->gateway_resource_objects current object=true) /\
  (forall description,gateway_resource_descriptions origin description=true->gateway_resource_descriptions current description=true) /\
  (forall object peer,gateway_resource_objects origin object=true->gateway_resource_peer origin object=Some peer->
    gateway_resource_peer current object=Some peer) /\
  gateway_resource_status_frame origin current(fun _=>False) /\gateway_exclusive_kept origin current.

Lemma gateway_resource_reference_refl state:gateway_resource_reference state state.
Proof.
  split;[auto|]. split;[auto|]. split;[auto|]. split;[auto|].
  split;[unfold gateway_resource_status_frame;intros;reflexivity|unfold gateway_exclusive_kept;intros;assumption].
Qed.

Lemma gateway_resource_reference_owned origin current fd entry:
  gateway_resource_reference origin current->gateway_owned_descriptor origin fd entry->gateway_owned_descriptor current fd entry.
Proof. intros[OWNED REST];apply OWNED. Qed.

Lemma gateway_resource_reference_object origin current object:
  gateway_resource_reference origin current->gateway_resource_objects origin object=true->gateway_resource_objects current object=true.
Proof. intros[_[OBJECT REST]];apply OBJECT. Qed.

Lemma gateway_resource_reference_step origin before after removed added:
  gateway_resource_reference origin before->gateway_resource_frame before after removed added->
  (forall fd entry,gateway_owned_descriptor origin fd entry->~removed fd)->
  gateway_resource_status_frame before after(fun _=>False)->gateway_exclusive_kept before after->
  gateway_resource_reference origin after.
Proof.
  intros[OWNED[OBJECTS[DESCRIPTIONS[PEERS[STATUS EXCLUSIVE]]]]]
    [KEEP[NEW[BIRTHS[DESCS PEER_FRAME]]]]NOT_REMOVED STATUS_AFTER EXCLUSIVE_AFTER.
  split.
  - intros fd entry OLD;apply KEEP;[apply OWNED;exact OLD|apply NOT_REMOVED with(entry:=entry);exact OLD].
  - split;[intros object OLD;apply BIRTHS,OBJECTS;exact OLD|].
    split;[intros description OLD;apply DESCS,DESCRIPTIONS;exact OLD|].
    split.
    + intros object peer LIVE EDGE;apply PEER_FRAME;[apply OBJECTS;exact LIVE|apply PEERS;assumption].
    + split.
      * intros fd entry OLD EX NONE.
        rewrite(STATUS_AFTER fd entry(OWNED fd entry OLD)(EXCLUSIVE _ EX)ltac:(tauto)).
        exact(STATUS fd entry OLD EX NONE).
      * intros description EX;apply EXCLUSIVE_AFTER,EXCLUSIVE;exact EX.
Qed.

Lemma gateway_resource_reference_from_frame before after removed added:
  gateway_resource_frame before after removed added->(forall fd entry,gateway_owned_descriptor before fd entry->~removed fd)->
  gateway_resource_status_frame before after(fun _=>False)->gateway_exclusive_kept before after->
  gateway_resource_reference before after.
Proof. intros FRAME KEPT STATUS EXCLUSIVE;eapply gateway_resource_reference_step;
  [apply gateway_resource_reference_refl|exact FRAME|exact KEPT|exact STATUS|exact EXCLUSIVE]. Qed.

Lemma gateway_resource_reference_transitive first second third:
  gateway_resource_reference first second->gateway_resource_reference second third->gateway_resource_reference first third.
Proof.
  intros[OWNED1[OBJECTS1[DESCRIPTIONS1[PEERS1[STATUS1 EXCLUSIVE1]]]]]
    [OWNED2[OBJECTS2[DESCRIPTIONS2[PEERS2[STATUS2 EXCLUSIVE2]]]]].
  split;[intros fd entry OLD;apply OWNED2,OWNED1;exact OLD|].
  split;[intros object OLD;apply OBJECTS2,OBJECTS1;exact OLD|].
  split;[intros description OLD;apply DESCRIPTIONS2,DESCRIPTIONS1;exact OLD|].
  split;[intros object peer LIVE EDGE;apply PEERS2;[apply OBJECTS1;exact LIVE|apply PEERS1;assumption]|].
  split.
  - intros fd entry OLD EX NONE.
    rewrite(STATUS2 fd entry(OWNED1 fd entry OLD)(EXCLUSIVE1 _ EX)ltac:(tauto));exact(STATUS1 fd entry OLD EX NONE).
  - intros description EX;apply EXCLUSIVE2,EXCLUSIVE1;exact EX.
Qed.

Lemma gateway_fresh_object_not_old_lease origin current fd entry object:
  gateway_resource_valid origin->gateway_resource_reference origin current->
  gateway_resource_objects origin object=false->gateway_resource_object(gateway_descriptor_object entry)=object->
  gateway_owned_descriptor current fd entry->
  forall previous,gateway_owned_descriptor origin fd previous->False.
Proof.
  intros[VALID DESCRIPTORS]REFERENCE FRESH OBJECT CURRENT previous OLD.
  pose proof(gateway_resource_reference_owned origin current fd previous REFERENCE OLD)as SAME.
  destruct CURRENT as[_ CURRENT];destruct SAME as[_ SAME];rewrite CURRENT in SAME;inversion SAME;subst previous.
  destruct(DESCRIPTORS fd entry(proj2 OLD))as[_[LIVE REST]].
  rewrite OBJECT,FRESH in LIVE;discriminate.
Qed.
