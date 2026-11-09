(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The fresh parent endpoint has one descriptor in the actual local table. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From EntryNamespace Require Import NamespaceObjects.
Open Scope Z_scope.

Definition unique_parent_endpoint(table:DescriptorTable)channel peer :=
  forall descriptor binding,table descriptor=Some binding ->
    descriptor_object binding=release_endpoint channel parent_endpoint ->descriptor=peer.

Theorem pair_has_unique_parent_endpoint before first second channel paired:
  socketpair_table before first second channel paired ->
  unique_parent_endpoint paired channel first.
Proof.
  intro PAIR;inversion PAIR;subst;unfold unique_parent_endpoint,table_put.
  intros descriptor binding PRESENT OBJECT.
  destruct(Int.eq descriptor second)eqn:SECOND.
  - inversion PRESENT;subst;discriminate.
  - destruct(Int.eq descriptor first)eqn:FIRST.
    + apply Int.same_if_eq;exact FIRST.
    + exfalso;eapply H4;eassumption.
Qed.

Theorem child_duplicate_preserves_unique_parent before source minimum result after channel peer:
  duplicate_table before source minimum result after ->
  before source=Some(endpoint_binding channel child_endpoint) ->
  unique_parent_endpoint before channel peer ->unique_parent_endpoint after channel peer.
Proof.
  intros DUP CHILD UNIQUE;inversion DUP;subst.
  assert(BINDING:binding=endpoint_binding channel child_endpoint)by congruence;subst binding.
  unfold unique_parent_endpoint,table_put;intros descriptor binding PRESENT OBJECT.
  destruct(Int.eq descriptor result).
  - inversion PRESENT;subst;discriminate.
  - eapply UNIQUE;eassumption.
Qed.

Theorem close_preserves_unique_parent before descriptor reply after channel peer:
  close_table before descriptor reply after ->unique_parent_endpoint before channel peer ->
  unique_parent_endpoint after channel peer.
Proof.
  intros CLOSE UNIQUE;inversion CLOSE;subst;try exact UNIQUE.
  all:unfold unique_parent_endpoint,table_remove;intros query binding PRESENT OBJECT;
    destruct(Int.eq query descriptor);[discriminate|eapply UNIQUE;eassumption].
Qed.

Theorem local_channel_has_unique_parent_endpoint before paired duplicated inherited
    first second failure channel reply:
  socketpair_table before first second channel paired ->
  duplicate_table paired second(Int.repr 60)failure duplicated ->
  close_table duplicated second reply inherited ->
  unique_parent_endpoint inherited channel first.
Proof.
  intros PAIR DUP CLOSE.
  eapply close_preserves_unique_parent;[exact CLOSE|].
  eapply child_duplicate_preserves_unique_parent;[exact DUP| |].
  - exact(proj1(pair_child_binding _ _ _ _ _ PAIR)).
  - eapply pair_has_unique_parent_endpoint;exact PAIR.
Qed.

Theorem unique_parent_excludes_other table channel peer descriptor:
  unique_parent_endpoint table channel peer ->descriptor<>peer ->
  excludes_parent_at table channel descriptor.
Proof.
  intros UNIQUE OTHER binding PRESENT OBJECT;apply OTHER;eapply UNIQUE;eassumption.
Qed.
