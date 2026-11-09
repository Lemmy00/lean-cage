(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The source's exact flag history determines the child table before image replacement. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine NativeHandoffTraceEvents.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace.
Import ListNotations.
Open Scope Z_scope.

Definition namespace_guest_event event:=namespace_process(process_entry event).
Definition namespace_good_flag tag:=match tag with
  |handoff_flag_event _ flags returned=>returned=Int.zero /\(flags=Int.zero\/flags=Int.one)
  |handoff_unexpected_event _=>False end.
Definition namespace_apply_flag world tag:=match tag with
  |handoff_flag_event descriptor flags _=>namespace_retable world
      (descriptor_flags(namespace_table world)descriptor(negb(Int.eq flags Int.zero)))
  |handoff_unexpected_event _=>world end.
Fixpoint namespace_apply_flags world tags:=match tags with
  |[]=>world|tag::rest=>namespace_apply_flags(namespace_apply_flag world tag)rest end.

Lemma namespace_empty_guest_event_frames before event after:
  namespace_kernel_event before(namespace_guest_event event)after ->handoff_event_flags event=[] ->after=before.
Proof.
  intros STEP EMPTY;inversion STEP;subst;cbn[namespace_guest_event handoff_event_flags]in EMPTY;
    try discriminate;reflexivity.
Qed.

Lemma namespace_projected_flag_is_actual event descriptor flags returned:
  handoff_event_flags event=[handoff_flag_event descriptor flags returned] ->
  event=entry_flags_returned descriptor flags returned.
Proof.
  intro PROJECTION;destruct event;cbn[handoff_event_flags]in PROJECTION;
    try discriminate;try solve[inversion PROJECTION;reflexivity].
  repeat match goal with
  | e:library_event|-_=>destruct e;cbn[handoff_event_flags]in PROJECTION;try discriminate
  | e:Machine.event|-_=>destruct e;cbn[handoff_event_flags]in PROJECTION;try discriminate
  | t:trace|-_=>destruct t;cbn[handoff_event_flags]in PROJECTION;discriminate
  end.
Qed.

Lemma namespace_single_guest_flag before event after tag:
  namespace_kernel_event before(namespace_guest_event event)after ->
  handoff_event_flags event=[tag] ->namespace_good_flag tag ->after=namespace_apply_flag before tag.
Proof.
  intros STEP PROJECTION GOOD.
  destruct tag as[descriptor flags returned|unexpected];cbn[namespace_good_flag]in GOOD;[|contradiction].
  apply namespace_projected_flag_is_actual in PROJECTION;subst event.
  destruct GOOD as[RETURNED FLAGS];subst returned.
  unfold namespace_guest_event in STEP;inversion STEP;subst;cbn[namespace_apply_flag namespace_flags_bit];
    try (cbn[namespace_passive_event]in *;discriminate);rewrite ?Int.eq_true;
    try reflexivity.
Qed.

Lemma namespace_guest_projection_shape event:
  handoff_event_flags event=[]\/exists tag,handoff_event_flags event=[tag].
Proof.
  destruct event;cbn[handoff_event_flags];eauto.
  destruct event;cbn[handoff_event_flags];eauto.
  destruct ev;cbn[handoff_event_flags];eauto.
  destruct t;cbn[handoff_event_flags];eauto.
Qed.

Theorem namespace_guest_flags_are_same_world before events after:
  namespace_kernel_steps before(map namespace_guest_event events)after ->
  Forall namespace_good_flag(handoff_flags_projection events) ->
  after=namespace_apply_flags before(handoff_flags_projection events).
Proof.
  revert before;induction events as[|event rest IH];intros before RUN GOOD;cbn in RUN;
    inversion RUN;subst;[reflexivity|].
  unfold handoff_flags_projection in *;cbn in GOOD|-*.
  destruct(namespace_guest_projection_shape event)as[EMPTY|[tag ONE]].
  - rewrite EMPTY in GOOD|-*;cbn in GOOD|-*.
    match goal with STEP:namespace_kernel_event _ _ _|-_=>
      pose proof(namespace_empty_guest_event_frames _ _ _ STEP EMPTY);subst middle end.
    apply IH;assumption.
  - rewrite ONE in GOOD|-*;cbn in GOOD|-*;inversion GOOD;subst.
    match goal with STEP:namespace_kernel_event _ _ _|-_=>
      pose proof(namespace_single_guest_flag _ _ _ _ STEP ONE H1);subst middle end.
    apply IH;assumption.
Qed.

Theorem expected_guest_flags_determine_table before events after input output errors failure:
  namespace_kernel_steps before(map namespace_guest_event events)after ->
  handoff_flags_projection events=handoff_expected_flags input output errors failure ->
  namespace_table after=handoff_stdio_table(namespace_table before)input output errors failure /\
  namespace_sigchld after=namespace_sigchld before /\
  namespace_signal_mask after=namespace_signal_mask before /\namespace_ambient after=namespace_ambient before.
Proof.
  intros RUN FLAGS.
  assert(GOOD:Forall namespace_good_flag(handoff_flags_projection events)).
  { rewrite FLAGS;unfold handoff_expected_flags.
    repeat (apply Forall_cons;[cbn[namespace_good_flag];auto|]);constructor. }
  pose proof(namespace_guest_flags_are_same_world _ _ _ RUN GOOD)as WORLD.
  rewrite FLAGS in WORLD;subst after;unfold handoff_expected_flags,namespace_apply_flags,namespace_apply_flag;
    cbn[namespace_retable];rewrite !Int.eq_true.
  rewrite Int.eq_false by (vm_compute;discriminate);repeat split;reflexivity.
Qed.
