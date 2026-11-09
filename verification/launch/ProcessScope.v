(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.image: A genuine close removes the owned cgroup object from the parent's authority. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
Require Import IO Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace.
Import ListNotations.

Definition object_absent (table:DescriptorTable) object :=
  forall fd binding,table fd=Some binding ->descriptor_object binding<>object.
Definition unique_object_alias (table:DescriptorTable) object descriptor :=
  forall fd binding,table fd=Some binding ->descriptor_object binding=object ->fd=descriptor.

Theorem successful_unique_close_removes_object before descriptor reply after object :
  unique_object_alias before object descriptor ->close_table before descriptor reply after ->
  close_value reply=Int.zero ->object_absent after object.
Proof.
  intros UNIQUE CLOSE ZERO;destruct reply;[|discriminate].
  inversion CLOSE;subst;intros fd binding LOOKUP SAME.
  unfold table_remove in LOOKUP;destruct(Int.eq fd descriptor)eqn:SELECTED;[discriminate|].
  assert(OTHER:fd<>descriptor)by(intro EQUAL;subst fd;rewrite Int.eq_true in SELECTED;discriminate).
  apply OTHER;eapply UNIQUE;eassumption.
Qed.

Lemma close_object_absent before descriptor reply after object :
  object_absent before object ->close_table before descriptor reply after ->object_absent after object.
Proof.
  intros ABSENT CLOSE;inversion CLOSE;subst;try exact ABSENT.
  all:intros fd binding LOOKUP;unfold table_remove in LOOKUP;
    destruct(Int.eq fd descriptor);[discriminate|eapply ABSENT;eassumption].
Qed.

Lemma duplicate_object_absent before descriptor minimum result after object :
  object_absent before object ->duplicate_table before descriptor minimum result after ->object_absent after object.
Proof.
  intros ABSENT DUP;inversion DUP;subst;intros fd other LOOKUP SAME.
  unfold table_put in LOOKUP;destruct(Int.eq fd result).
  - inversion LOOKUP;subst other;cbn in SAME;eapply ABSENT;eassumption.
  - eapply ABSENT;eassumption.
Qed.

Lemma pair_ordinary_absent before first second channel after object :
  object_absent before(ordinary_object object) ->socketpair_table before first second channel after ->
  object_absent after(ordinary_object object).
Proof.
  intros ABSENT PAIR;inversion PAIR;subst;intros fd binding LOOKUP SAME.
  unfold table_put in LOOKUP;destruct(Int.eq fd second).
  - inversion LOOKUP;subst binding;cbn in SAME;discriminate.
  - destruct(Int.eq fd first).
    + inversion LOOKUP;subst binding;cbn in SAME;discriminate.
    + eapply ABSENT;eassumption.
Qed.

Lemma flags_object_absent table fd flag object : object_absent table object ->
  object_absent(descriptor_flags table fd flag)object.
Proof.
  intros ABSENT query binding LOOKUP SAME;unfold descriptor_flags in LOOKUP.
  destruct(table query)as[old|]eqn:OLD;[|discriminate].
  destruct(Int.eq query fd);inversion LOOKUP;subst binding;cbn in SAME;eapply ABSENT;eassumption.
Qed.

Lemma exec_object_absent table object : object_absent table object ->object_absent(exec_table table)object.
Proof.
  intros ABSENT fd binding LOOKUP;unfold exec_table in LOOKUP.
  destruct(table fd)as[old|]eqn:OLD;[|discriminate].
  destruct(descriptor_cloexec old);[discriminate|]. inversion LOOKUP;subst;eapply ABSENT;exact OLD.
Qed.

(* These are the declared namespace operations, not all Linux calls. The
   post-release source closure separately excludes open and descriptor receipt. *)
Theorem namespace_ordinary_absence_step before event after object :
  namespace_kernel_event before event after ->
  object_absent(namespace_table before)(ordinary_object object) ->
  object_absent(namespace_table after)(ordinary_object object).
Proof.
  intros STEP ABSENT;inversion STEP;subst;cbn;try exact ABSENT;
    try solve[eapply pair_ordinary_absent;eassumption];
    try solve[eapply duplicate_object_absent;eassumption];
    try solve[eapply close_object_absent;eassumption];
    try solve[apply flags_object_absent;exact ABSENT];
    try solve[apply exec_object_absent;exact ABSENT].
  all:try match goal with FORK:namespace_fork_effect _ _ _ _|-_=>inversion FORK;subst;exact ABSENT end.
  all:try match goal with |-object_absent(namespace_table(namespace_default_action _ ?signal))_=>
    unfold namespace_default_action;destruct(Int.eq signal(Int.repr 17));exact ABSENT end.
  intros fd binding IMPOSSIBLE;discriminate.
Qed.

Theorem namespace_ordinary_absence_trace before events after object :
  namespace_kernel_steps before events after ->
  object_absent(namespace_table before)(ordinary_object object) ->
  object_absent(namespace_table after)(ordinary_object object).
Proof.
  intro RUN;induction RUN;intro ABSENT;[exact ABSENT|].
  apply IHRUN;eapply namespace_ordinary_absence_step;eassumption.
Qed.

Theorem actual_closed_cgroup_stays_absent before descriptor reply after prefix final object :
  unique_object_alias(namespace_table before)(ordinary_object object)descriptor ->
  namespace_kernel_event before(namespace_process(process_entry(entry_library(close_returned descriptor reply))))after ->
  close_value reply=Int.zero ->namespace_kernel_steps after prefix final ->
  object_absent(namespace_table final)(ordinary_object object).
Proof.
  intros UNIQUE CLOSE ZERO RUN.
  destruct(namespace_close_kernel_details _ _ _ _ CLOSE)as[table[CLOSED WORLD]];subst after.
  eapply namespace_ordinary_absence_trace;[exact RUN|].
  eapply successful_unique_close_removes_object;eassumption.
Qed.
