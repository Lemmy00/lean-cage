(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Physical descriptors, caller leases and OFDs retain distinct identities. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values.
From HostGateway Require Import GatewaySpawnDescriptors.
Import ListNotations.
Open Scope Z_scope.

Record gateway_open_description := {
  gateway_resource_object : nat;
  gateway_resource_description : nat
}.

Definition gateway_resource_descriptor := gateway_descriptor gateway_open_description.

Record gateway_resource_state := {
  gateway_resource_descriptors : gateway_descriptor_table gateway_open_description;
  gateway_resource_owned : Z -> bool;
  gateway_resource_objects : nat -> bool;
  gateway_resource_descriptions : nat -> bool;
  gateway_resource_description_object : nat -> option nat;
  gateway_resource_nonblocking : nat -> bool;
  gateway_resource_exclusive : nat -> bool;
  (* Immutable birth topology, including after shutdown/close; not liveness. *)
  gateway_resource_peer : nat -> option nat
}.

(* Ownership is relative to this invocation, like native_private. Other live
   descriptors may change during a call; the numeric slot itself is not a lease. *)
Definition gateway_resource_valid (state : gateway_resource_state) : Prop :=
  (forall fd, gateway_resource_owned state fd = true ->
    exists entry, gateway_resource_descriptors state fd = Some entry) /\
  forall fd entry, gateway_resource_descriptors state fd = Some entry ->
    0 <= fd <= Int.max_signed /\
    gateway_resource_objects state (gateway_resource_object (gateway_descriptor_object entry)) = true /\
    gateway_resource_descriptions state (gateway_resource_description (gateway_descriptor_object entry)) = true /\
    gateway_resource_description_object state (gateway_resource_description (gateway_descriptor_object entry)) =
      Some (gateway_resource_object (gateway_descriptor_object entry)).

Definition gateway_owned_descriptor (state : gateway_resource_state) fd entry : Prop :=
  gateway_resource_owned state fd = true /\ gateway_resource_descriptors state fd = Some entry.

Definition gateway_resource_frame (before after : gateway_resource_state) (removed added : Z -> Prop) : Prop :=
  (forall fd entry, gateway_owned_descriptor before fd entry -> ~ removed fd ->
    gateway_owned_descriptor after fd entry) /\
  (forall fd, gateway_resource_owned after fd = true -> gateway_resource_owned before fd = true \/ added fd) /\
  (forall object, gateway_resource_objects before object = true -> gateway_resource_objects after object = true) /\
  (forall description, gateway_resource_descriptions before description = true ->
    gateway_resource_descriptions after description = true) /\
  (forall object peer, gateway_resource_objects before object = true ->
    gateway_resource_peer before object = Some peer ->
    gateway_resource_peer after object = Some peer).

Definition gateway_resource_status_frame (before after : gateway_resource_state) (changed : nat -> Prop) : Prop :=
  forall fd entry, gateway_owned_descriptor before fd entry ->
    gateway_resource_exclusive before (gateway_resource_description (gateway_descriptor_object entry)) = true ->
    ~ changed (gateway_resource_description (gateway_descriptor_object entry)) ->
    gateway_resource_nonblocking after (gateway_resource_description (gateway_descriptor_object entry)) =
      gateway_resource_nonblocking before (gateway_resource_description (gateway_descriptor_object entry)).

Definition gateway_socket_descriptor object description : gateway_resource_descriptor :=
  {| gateway_descriptor_object := {| gateway_resource_object := object; gateway_resource_description := description |};
     gateway_descriptor_cloexec := true |}.

Record gateway_socketpair_receipt (ipc : nat -> Prop) (before after : gateway_resource_state) : Type := {
  gateway_pair_left : Z;
  gateway_pair_right : Z;
  gateway_pair_left_object : nat;
  gateway_pair_right_object : nat;
  gateway_pair_left_description : nat;
  gateway_pair_right_description : nat;
  gateway_pair_left_width : 0 <= gateway_pair_left <= Int.max_signed;
  gateway_pair_right_width : 0 <= gateway_pair_right <= Int.max_signed;
  gateway_pair_slots_separate : gateway_pair_left <> gateway_pair_right;
  gateway_pair_left_unleased : gateway_resource_owned before gateway_pair_left = false;
  gateway_pair_right_unleased : gateway_resource_owned before gateway_pair_right = false;
  gateway_pair_objects_separate : gateway_pair_left_object <> gateway_pair_right_object;
  gateway_pair_descriptions_separate : gateway_pair_left_description <> gateway_pair_right_description;
  gateway_pair_left_fresh : gateway_resource_objects before gateway_pair_left_object = false;
  gateway_pair_right_fresh : gateway_resource_objects before gateway_pair_right_object = false;
  gateway_pair_left_description_fresh : gateway_resource_descriptions before gateway_pair_left_description = false;
  gateway_pair_right_description_fresh : gateway_resource_descriptions before gateway_pair_right_description = false;
  gateway_pair_left_live : gateway_owned_descriptor after gateway_pair_left
    (gateway_socket_descriptor gateway_pair_left_object gateway_pair_left_description);
  gateway_pair_right_live : gateway_owned_descriptor after gateway_pair_right
    (gateway_socket_descriptor gateway_pair_right_object gateway_pair_right_description);
  gateway_pair_left_ipc : ipc gateway_pair_left_object;
  gateway_pair_right_ipc : ipc gateway_pair_right_object;
  gateway_pair_left_nonblocking : gateway_resource_nonblocking after gateway_pair_left_description = true;
  gateway_pair_right_nonblocking : gateway_resource_nonblocking after gateway_pair_right_description = true;
  gateway_pair_left_exclusive : gateway_resource_exclusive after gateway_pair_left_description = true;
  gateway_pair_right_exclusive : gateway_resource_exclusive after gateway_pair_right_description = true;
  gateway_pair_left_connected : gateway_resource_peer after gateway_pair_left_object = Some gateway_pair_right_object;
  gateway_pair_right_connected : gateway_resource_peer after gateway_pair_right_object = Some gateway_pair_left_object;
  gateway_pair_other_leases : gateway_resource_frame before after (fun _ => False)
    (fun fd => fd = gateway_pair_left \/ fd = gateway_pair_right);
  gateway_pair_other_status : gateway_resource_status_frame before after (fun _ => False)
}.

Record gateway_duplicate_receipt (before after : gateway_resource_state) source minimum returned entry : Prop := {
  gateway_duplicate_source : gateway_owned_descriptor before source entry;
  gateway_duplicate_width : minimum <= returned <= Int.max_signed;
  gateway_duplicate_nonnegative : 0 <= returned;
  gateway_duplicate_unleased : gateway_resource_owned before returned = false;
  gateway_duplicate_live : gateway_owned_descriptor after returned
    {| gateway_descriptor_object := gateway_descriptor_object entry; gateway_descriptor_cloexec := true |};
  gateway_duplicate_frame : gateway_resource_frame before after (fun _ => False) (fun fd => fd = returned);
  gateway_duplicate_status : gateway_resource_status_frame before after (fun _ => False)
}.

Lemma gateway_duplicate_keeps_source before after source minimum returned entry :
  gateway_duplicate_receipt before after source minimum returned entry -> gateway_owned_descriptor after source entry.
Proof.
  intro RECEIPT; eapply (proj1 (gateway_duplicate_frame _ _ _ _ _ _ RECEIPT));
    [exact (gateway_duplicate_source _ _ _ _ _ _ RECEIPT) |tauto].
Qed.

Lemma gateway_duplicate_slot_distinct before after source minimum returned entry :
  gateway_duplicate_receipt before after source minimum returned entry -> returned <> source.
Proof.
  intros RECEIPT SAME; subst returned.
  pose proof (proj1 (gateway_duplicate_source _ _ _ _ _ _ RECEIPT)) as LIVE.
  rewrite (gateway_duplicate_unleased _ _ _ _ _ _ RECEIPT) in LIVE; discriminate.
Qed.
