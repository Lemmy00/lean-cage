(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Actual post-fork operations retain descriptor-object provenance. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceObjects NamespaceEndpoint NamespaceMachine NamespaceKernel NamespaceWorldTrace.
Import ListNotations.

Definition descriptor_object_frame(before after:DescriptorTable):Prop:=forall fd binding,
  after fd=Some binding ->exists previous,before fd=Some previous /\
    descriptor_object previous=descriptor_object binding.

Lemma descriptor_object_frame_refl table:descriptor_object_frame table table.
Proof. intros fd binding PRESENT;exists binding;auto. Qed.
Lemma descriptor_object_frame_trans before middle after:
  descriptor_object_frame before middle ->descriptor_object_frame middle after ->descriptor_object_frame before after.
Proof.
  intros FIRST SECOND fd binding PRESENT;destruct(SECOND _ _ PRESENT)as[mid[OLD OBJECT]].
  destruct(FIRST _ _ OLD)as[original[PRIOR SAME]];exists original;split;[exact PRIOR|congruence].
Qed.
Lemma descriptor_close_object_frame before fd reply after:
  close_table before fd reply after ->descriptor_object_frame before after.
Proof.
  intro CLOSE;inversion CLOSE;subst;try apply descriptor_object_frame_refl.
  all:intros query binding PRESENT;unfold table_remove in PRESENT;
    destruct(Int.eq query fd);[discriminate|exists binding;auto].
Qed.
Lemma descriptor_flags_object_frame table fd flag:
  descriptor_object_frame table(descriptor_flags table fd flag).
Proof. intros query binding PRESENT;exact(flags_preserve_object _ _ _ _ _ PRESENT). Qed.
Lemma descriptor_exec_object_frame table:descriptor_object_frame table(exec_table table).
Proof.
  intros fd binding PRESENT;unfold exec_table in PRESENT.
  destruct(table fd)as[old|]eqn:OLD;[|discriminate].
  destruct(descriptor_cloexec old);[discriminate|inversion PRESENT;subst;exists binding;auto].
Qed.
Lemma descriptor_empty_object_frame table:descriptor_object_frame table(fun _=>None).
Proof. intros fd binding;discriminate. Qed.

Theorem namespace_process_object_frame before event after:
  namespace_kernel_event before(namespace_process event)after ->
  descriptor_object_frame(namespace_table before)(namespace_table after).
Proof.
  intro OPERATION;inversion OPERATION;subst;cbn[namespace_retable namespace_exec namespace_table];
    try apply descriptor_object_frame_refl.
  - eapply descriptor_close_object_frame;eassumption.
  - apply descriptor_flags_object_frame.
  - apply descriptor_flags_object_frame.
  - apply descriptor_exec_object_frame.
  - apply descriptor_empty_object_frame.
  - apply descriptor_flags_object_frame.
Qed.

Definition namespace_after_fork_event event:=match event with
  |namespace_process _|namespace_waiting=>true|_=>false end.

Theorem namespace_after_fork_object_frame before events after:
  Forall(fun event=>namespace_after_fork_event event=true)events ->
  namespace_kernel_steps before events after ->
  descriptor_object_frame(namespace_table before)(namespace_table after).
Proof.
  intros EVENTS RUN;induction RUN;[apply descriptor_object_frame_refl|].
  inversion EVENTS;subst;eapply descriptor_object_frame_trans;[|apply IHRUN;assumption].
  destruct event;try discriminate.
  - eapply namespace_process_object_frame;eassumption.
  - inversion H;subst;try discriminate;apply descriptor_object_frame_refl.
Qed.

Theorem descriptor_frame_preserves_unique_parent before after channel peer:
  descriptor_object_frame before after ->unique_parent_endpoint before channel peer ->
  unique_parent_endpoint after channel peer.
Proof.
  intros FRAME UNIQUE fd binding PRESENT OBJECT.
  destruct(FRAME _ _ PRESENT)as[previous[OLD SAME]];eapply UNIQUE;[exact OLD|congruence].
Qed.
Theorem descriptor_frame_preserves_exclusion before after channel fd:
  descriptor_object_frame before after ->excludes_parent_at before channel fd ->excludes_parent_at after channel fd.
Proof.
  intros FRAME EXCLUDES binding PRESENT OBJECT;destruct(FRAME _ _ PRESENT)as[previous[OLD SAME]].
  eapply EXCLUDES;[exact OLD|congruence].
Qed.
Theorem descriptor_frame_preserves_absence before after channel:
  descriptor_object_frame before after ->channel_absent before channel ->channel_absent after channel.
Proof.
  intros FRAME ABSENT fd binding side PRESENT OBJECT;destruct(FRAME _ _ PRESENT)as[previous[OLD SAME]].
  exact(ABSENT fd previous side OLD(eq_trans SAME OBJECT)).
Qed.
