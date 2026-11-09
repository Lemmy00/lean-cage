(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: The actual pre-admission closes preserve the distinct prepared cgroup descriptor. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace NamespaceParentEntry.
Import ListNotations.

Lemma prelude_close_other before closed reply after fd binding:
  close_table before closed reply after ->fd<>closed ->before fd=Some binding ->after fd=Some binding.
Proof.
  intros CLOSE OTHER PRESENT;inversion CLOSE;subst;try exact PRESENT.
  all:unfold table_remove;rewrite Int.eq_false by exact OTHER;exact PRESENT.
Qed.

Theorem namespace_prelude_slot_step before event after fd binding:
  namespace_parent_prelude_event event=true ->namespace_parent_closed_fd event<>Some fd ->
  namespace_kernel_event before event after ->namespace_table before fd=Some binding ->
  namespace_table after fd=Some binding.
Proof.
  intros PRELUDE NOT_CLOSED STEP PRESENT;inversion STEP;subst;
    try exact PRESENT;try discriminate PRELUDE.
  - cbn[namespace_table namespace_retable].
    eapply prelude_close_other;[eassumption| |exact PRESENT].
    intro SAME;apply NOT_CLOSED;change(Some descriptor=Some fd);congruence.
Qed.

Theorem namespace_prelude_slot_steps before events after fd binding:
  Forall(fun event=>namespace_parent_prelude_event event=true)events ->
  Forall(fun event=>namespace_parent_closed_fd event<>Some fd)events ->
  namespace_kernel_steps before events after ->namespace_table before fd=Some binding ->
  namespace_table after fd=Some binding.
Proof.
  intros PRELUDE NOT_CLOSED RUN;induction RUN;intro PRESENT;[exact PRESENT|].
  inversion PRELUDE;inversion NOT_CLOSED;subst;apply IHRUN;try assumption.
  eapply namespace_prelude_slot_step;eassumption.
Qed.

Lemma namespace_prelude_closes_exclude descriptors events fd:
  Forall(namespace_parent_closes_from descriptors)events ->~In fd descriptors ->
  Forall(fun event=>namespace_parent_closed_fd event<>Some fd)events.
Proof.
  intros CLOSED OUTSIDE;apply Forall_forall;intros event MEMBER ACTUAL.
  apply OUTSIDE;apply Forall_forall with(x:=event)in CLOSED;[exact(CLOSED fd ACTUAL)|exact MEMBER].
Qed.
