(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The same actual source image closes every inherited grant-writer alias. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffTraceEvents NativeHandoffTrace.
From EntryNative Require Import NativeHandoffGuest NativeHandoffImage NativeHandoffLoop NativeHandoffMemory.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace
  NamespaceGuestFlags NamespaceGuest.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Lemma namespace_entry_runs_are_preserved ge cell before events after:
  entry_handoff_steps ge cell before events after ->
  namespace_steps ge cell before(map namespace_guest_event events)after.
Proof.
  intro RUN;induction RUN;cbn;[constructor|].
  econstructor;[apply namespace_process_step,process_entry_step;exact H|exact IHRUN].
Qed.

Theorem actual_namespace_image_checked_handles cell input before input_fd output_fd errors_fd failure k
    events target path arguments environment:
  handoff_borrowed_input cell before input ->
  namespace_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))events target ->
  In(namespace_guest_event(entry_image path arguments environment))events ->
  Forall(fun fd=>4<=Int.signed fd)[input_fd;output_fd;errors_fd;failure].
Proof.
  intros INPUT RUN IMAGE.
  destruct(actual_namespace_guest_projects _ _ _ _ _ _ _ _ _ _ INPUT RUN)as[actual[EVENTS REAL]].
  subst events.
  assert(OBSERVED:In(entry_image path arguments environment)actual).
  { apply in_map_iff in IMAGE;destruct IMAGE as[event[SAME MEMBER]];inversion SAME;subst;exact MEMBER. }
  destruct(handoff_guest_image_has_checked_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT REAL OBSERVED)
    as[prefix[endpoint[rest[EVENTS[NOIMAGES[PRE[SNAPSHOT POST]]]]]]].
  destruct SNAPSHOT as[b[after[caller[uidbytes[fdtexts[suffix[SAME[FAILURE FIELDS]]]]]]]].
  destruct FIELDS as[LIVE[MODE[UID[UIDTEXT[UIDLEN[UIDVALUE[HISTORY[HISTORYLEN[CHECKED TABLES]]]]]]]]].
  pose proof(proj1(CHECKED 0 ltac:(lia)))as INPUT_FD.
  pose proof(proj1(CHECKED 1 ltac:(lia)))as OUTPUT_FD.
  pose proof(proj1(CHECKED 2 ltac:(lia)))as ERRORS_FD.
  pose proof(proj1(CHECKED 3 ltac:(lia)))as FAILURE_FD.
  cbn[handoff_original_words]in INPUT_FD,OUTPUT_FD,ERRORS_FD,FAILURE_FD.
  repeat constructor;assumption.
Qed.

Lemma namespace_waits_then_image_table before waits path arguments environment after:
  namespace_kernel_steps before(map namespace_guest_event
    (repeat entry_primitive_wait waits++[entry_image path arguments environment]))after ->
  namespace_table after=exec_table(namespace_table before).
Proof.
  revert before;induction waits as[|waits IH];intros before RUN;cbn in RUN.
  - inversion RUN;subst.
    match goal with TAIL:namespace_kernel_steps _ [] _|-_=>inversion TAIL;subst;clear TAIL end.
    match goal with IMAGE:namespace_kernel_event _ (namespace_guest_event(entry_image _ _ _)) _|-_=>
      inversion IMAGE;subst;cbn[namespace_guest_event namespace_exec namespace_retable];try reflexivity;
      match goal with PASSIVE:namespace_passive_event _=true|-_=>discriminate PASSIVE end end.
  - inversion RUN;subst.
    match goal with WAIT:namespace_kernel_event _ (namespace_guest_event entry_primitive_wait) _|-_=>
      pose proof(namespace_empty_guest_event_frames _ _ _ WAIT eq_refl);subst middle end.
    apply IH;eassumption.
Qed.

Theorem actual_namespace_image_has_private_table cell input before input_fd output_fd errors_fd failure k
    events target path arguments environment before_world after_world channel:
  handoff_borrowed_input cell before input ->
  namespace_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))events target ->
  In(namespace_guest_event(entry_image path arguments environment))events ->
  namespace_kernel_steps before_world events after_world ->
  parent_channel_cloexec(namespace_table before_world)channel ->
  excludes_parent_at(namespace_table before_world)channel input_fd ->
  excludes_parent_at(namespace_table before_world)channel output_fd ->
  excludes_parent_at(namespace_table before_world)channel errors_fd ->
  excludes_parent_at(namespace_table before_world)channel failure ->
  namespace_table after_world=
    exec_table(handoff_stdio_table(namespace_table before_world)input_fd output_fd errors_fd failure) /\
  (forall descriptor binding,namespace_table after_world descriptor=Some binding ->
    descriptor_object binding<>release_endpoint channel parent_endpoint).
Proof.
  intros INPUT RUN IMAGE KERNEL CLOEXEC INPUT_EXCLUDES OUTPUT_EXCLUDES ERRORS_EXCLUDES FAILURE_EXCLUDES.
  destruct(actual_namespace_guest_projects _ _ _ _ _ _ _ _ _ _ INPUT RUN)as[actual[EVENTS REAL]].
  subst events.
  assert(OBSERVED:In(entry_image path arguments environment)actual).
  { apply in_map_iff in IMAGE;destruct IMAGE as[event[SAME MEMBER]].
    inversion SAME;subst event;exact MEMBER. }
  destruct(handoff_guest_image_flags _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT REAL OBSERVED)
    as[prefix[b[after[caller[suffix[waits[EVENTS[FLAGS[PRE[PATH[ARGS[ENV TARGET]]]]]]]]]]]].
  rewrite EVENTS,map_app in KERNEL.
  destruct(namespace_kernel_steps_split _ _ _ _ KERNEL)as[at_exec[PREFIX REPLACEMENT]].
  destruct(expected_guest_flags_determine_table _ _ _ _ _ _ _ PREFIX FLAGS)
    as[TABLE[DEFAULT[MASK AMBIENT]]].
  pose proof(namespace_waits_then_image_table _ _ _ _ _ _ REPLACEMENT)as FINAL.
  rewrite TABLE in FINAL;split;[exact FINAL|].
  intros descriptor binding PRESENT;rewrite FINAL in PRESENT.
  exact(actual_handoff_exec_has_no_grant_writer(namespace_table before_world)
    input_fd output_fd errors_fd failure channel CLOEXEC INPUT_EXCLUDES OUTPUT_EXCLUDES
    ERRORS_EXCLUDES FAILURE_EXCLUDES descriptor binding PRESENT).
Qed.
