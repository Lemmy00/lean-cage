(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: An unexpected returning exec enters the actual non-returning failure path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine StoreSteps ClightSteps LibraryMachine ErrorNumber.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure
  NativeHandoffArguments NativeHandoffExec NativeHandoffCount HandoffRegion.
From EntryNative Require Import NativeHandoffAllocation.
From EntryNative Require Import NativeHandoffGuest NativeHandoffEncoding NativeHandoffInput.
From EntryFailure Require Import FailureSource FailureMachine.
Import ListNotations.
Open Scope Z_scope.

Lemma handoff_exec_library_loss ge cell path arguments environment k before event target :
  library_step ge cell
    (live(Callstate entry_exec_definition[path;arguments;environment]k before))event target ->
  event=original_event loss_step /\target=dead before.
Proof.
  intros STEP;inversion STEP;subst;try discriminate.
  - inversion H;subst;cbn in *;try contradiction;auto;
      match goal with BOUNDARY:boundary _ _ _ |- _ =>
        inversion BOUNDARY;subst;destruct(operation q);discriminate end.
  - match goal with READY:library_ready _ _ |- _ =>inversion READY end.
Qed.




Theorem handoff_exec_cases ge cell path arguments environment k before event target :
  entry_handoff_step ge cell
    (live(Callstate entry_exec_definition[path;arguments;environment]k before))event target ->
  (exists returned after,entry_errno_frame cell before after /\entry_errno_ready cell after /\
    event=entry_exec_returned path arguments environment returned /\
    target=live(Returnstate(Vint returned)k after)) \/
  (event=entry_primitive_wait /\target=live(Callstate entry_exec_definition[path;arguments;environment]k before)) \/
  (exists after,entry_errno_partial cell before after /\
    event=entry_exec_lost path arguments environment /\target=dead after) \/
  (event=entry_library(original_event loss_step) /\target=dead before) \/
  (event=entry_image path arguments environment /\target=dead before).
Proof.
  intros STEP;inversion STEP;subst;try discriminate.
  - destruct(handoff_exec_library_loss _ _ _ _ _ _ _ _ _ H)as[EVENT TARGET];subst;auto 8.
  - left;exists returned,after;auto.
  - right;right;left;exists after;auto.
  - right;right;right;right;auto.
  - right;left;auto.
Qed.

Theorem handoff_failure_call_has_no_image cell base failure stage error suffix events target :
  entry_errno_ready cell base ->is_call_cont suffix ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal f_fail_child)[Vint failure;Vint stage;Vint error]suffix base))events target ->
  forall path arguments environment,~In(entry_image path arguments environment)events.
Proof.
  intros ERRNO CALL RUN.
  change(entry_handoff_steps failure_ge cell
    (live(failure_initial failure stage error suffix base))events target)in RUN.
  exact(proj2(current_entry_failure_caller_prefix _ _ _ _ _ _ _ _
    (entry_errno_ready_tls _ _ ERRNO)CALL RUN)).
Qed.

Lemma handoff_exec_error_tail_actual : guest_tail 24(fn_body f_guest)=
  handoff_error_failure_program _t'21 Int.one.
Proof. reflexivity. Qed.

Theorem handoff_exec_return_failure_region cell b caller after returned failure k :
  caller!_failure=Some(Vint failure) ->entry_errno_ready cell after ->
  handoff_region handoff_ge cell(fun _=>True)
    (fun state=>exists error final,
      state=Callstate(Internal f_fail_child)[Vint failure;Vint Int.one;Vint error]
        (Kcall None f_guest(handoff_locals_env b)final k)after /\
      1<=Int.signed error<=4095)130
    (Returnstate(Vint returned)
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))k))after).
Proof.
  intros FAILURE ERRNO;unfold handoff_exec_cont.
  eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
  eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
  rewrite handoff_exec_error_tail_actual at 1.
  replace 128%nat with(128+0)%nat at 1 by lia.
  eapply handoff_region_bind with(n:=128%nat)(extra:=0%nat).
  - apply handoff_error_failure_region.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + discriminate.
    + cbn[set_opttemp];rewrite PTree.gso by discriminate;exact FAILURE.
    + exact ERRNO.
    + exact I.
  - intros endpoint[error[RANGE SAME]].
    apply handoff_region_stop;[exact I|]. exists error; eexists;split;[exact SAME|exact RANGE].
Qed.

Theorem handoff_returning_exec_has_no_image cell b caller after returned failure k events target :
  caller!_failure=Some(Vint failure) ->entry_errno_ready cell after ->
  entry_handoff_steps handoff_ge cell
    (live(Returnstate(Vint returned)
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))k))after))events target ->
  forall path arguments environment,~In(entry_image path arguments environment)events.
Proof.
  intros FAILURE ERRNO RUN path arguments environment IMAGE.
  destruct(handoff_region_image_requires_leaf _ _ _ _ _ _ _ _ _ _ _
    (handoff_exec_return_failure_region cell b caller after returned failure k FAILURE ERRNO)RUN IMAGE)
    as[prefix[endpoint[rest[EVENTS[NOIMAGES[PREFIX[MEMORY[RESULT TAIL]]]]]]]].
  destruct RESULT as[error[final[SAME RANGE]]];subst endpoint.
  rewrite EVENTS in IMAGE;apply in_app_iff in IMAGE;destruct IMAGE as[EARLY|LATER].
  - unfold handoff_no_images in NOIMAGES;rewrite Forall_forall in NOIMAGES.
    specialize(NOIMAGES _ EARLY);discriminate.
  - exact(handoff_failure_call_has_no_image cell after failure Int.one error
      (Kcall None f_guest(handoff_locals_env b)final k)rest target ERRNO I TAIL
      path arguments environment LATER).
Qed.

Theorem handoff_exec_image_is_current cell b caller before failure k path arguments environment
    events target viewed_path viewed_arguments viewed_environment :
  caller!_failure=Some(Vint failure) ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate entry_exec_definition[path;arguments;environment]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))k))before))
    events target ->
  In(entry_image viewed_path viewed_arguments viewed_environment)events ->
  viewed_path=path /\viewed_arguments=arguments /\viewed_environment=environment /\
    exists waits,events=repeat entry_primitive_wait waits++[entry_image path arguments environment] /\
      target=dead before.
Proof.
  intros FAILURE;revert target.
  induction events as[|event events IH];intros target RUN IMAGE;[contradiction|].
  inversion RUN;subst.
  match goal with STEP:entry_handoff_step _ _ _ _ _ |- _ =>
    destruct(handoff_exec_cases _ _ _ _ _ _ _ _ _ STEP)
      as[[returned[after[FRAME[ERRNO[EVENT TARGET]]]]]|[[EVENT TARGET]|
        [[after[PARTIAL[EVENT TARGET]]]|[[EVENT TARGET]|[EVENT TARGET]]]]]end;subst.
  - destruct IMAGE as[SAME|LATER];[discriminate|].
    exfalso;eapply handoff_returning_exec_has_no_image;
      [exact FAILURE|exact ERRNO|eassumption|exact LATER].
  - destruct IMAGE as[SAME|LATER];[discriminate|].
    match goal with TAIL:entry_handoff_steps _ _ _ events target |- _ =>
      destruct(IH target TAIL LATER)as[PATH[ARGUMENTS[ENVIRONMENT[waits[EVENTS TARGET]]]]]end.
    repeat split;try assumption;exists(S waits);cbn;split;[rewrite EVENTS;reflexivity|exact TARGET].
  - match goal with TAIL:entry_handoff_steps _ _ (dead _) events target |- _ =>
      destruct(entry_handoff_dead_steps _ _ _ _ _ TAIL)as[EVENTS TARGET]end;subst.
    destruct IMAGE as[SAME|NONE];[discriminate|contradiction].
  - match goal with TAIL:entry_handoff_steps _ _ (dead _) events target |- _ =>
      destruct(entry_handoff_dead_steps _ _ _ _ _ TAIL)as[EVENTS TARGET]end;subst.
    destruct IMAGE as[SAME|NONE];[discriminate|contradiction].
  - match goal with TAIL:entry_handoff_steps _ _ (dead _) events target |- _ =>
      destruct(entry_handoff_dead_steps _ _ _ _ _ TAIL)as[EVENTS TARGET]end;subst.
    destruct IMAGE as[SAME|NONE];[inversion SAME;subst|contradiction].
    repeat split;try reflexivity;exists 0%nat;split;reflexivity.
Qed.

(* The snapshot below is reached by this very source execution, rather than by
   an independently chosen successful formatter or executor transcript. *)
Theorem handoff_guest_image_has_checked_snapshot cell input before
    input_fd output_fd errors_fd failure k events target path arguments environment :
  handoff_borrowed_input cell before input ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal f_guest)
      [Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))events target ->
  In(entry_image path arguments environment)events ->
  exists prefix endpoint rest,
    events=prefix++rest /\ handoff_no_images prefix /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal f_guest)
        [Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))prefix(live endpoint) /\
    handoff_image_snapshot cell input input_fd output_fd errors_fd failure endpoint /\
    entry_handoff_steps handoff_ge cell(live endpoint)rest target /\
    In(entry_image path arguments environment)rest.
Proof.
  intros INPUT RUN IMAGE.
  destruct(handoff_region_image_requires_leaf _ _ _ _ _ _ _ _ _ _ _
    (handoff_guest_region cell input before input_fd output_fd errors_fd failure k INPUT)RUN IMAGE)
    as[prefix[endpoint[rest[EVENTS[NOIMAGES[PREFIX[MEMORY[RESULT TAIL]]]]]]]].
  assert(LATER:In(entry_image path arguments environment)rest).
  { rewrite EVENTS in IMAGE;apply in_app_iff in IMAGE;destruct IMAGE as[EARLY|LATER];[|exact LATER].
    unfold handoff_no_images in NOIMAGES;rewrite Forall_forall in NOIMAGES.
    specialize(NOIMAGES _ EARLY);discriminate. }
  destruct RESULT as[FAILURE|SNAPSHOT].
  - destruct FAILURE as[stage[error[suffix[after[SAME[STAGE[ERROR[ERRNO CALL]]]]]]]];subst endpoint.
    exfalso;exact(handoff_failure_call_has_no_image cell after failure stage error suffix rest target
      ERRNO CALL TAIL path arguments environment LATER).
  - exists prefix,endpoint,rest;auto 8.
Qed.

Theorem handoff_guest_image_current cell input before
    input_fd output_fd errors_fd failure k events target path arguments environment :
  handoff_borrowed_input cell before input ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal f_guest)
      [Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))events target ->
  In(entry_image path arguments environment)events ->
  exists prefix b after caller suffix waits,
    path=Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero /\
    arguments=Vptr(handoff_arguments b)Ptrofs.zero /\
    environment=Vptr(handoff_environment b)Ptrofs.zero /\
    events=prefix++(repeat entry_primitive_wait waits++[entry_image path arguments environment]) /\
    handoff_no_images prefix /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal f_guest)
        [Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))prefix
      (live(Callstate entry_exec_definition[path;arguments;environment]
        (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))suffix))after)) /\
    handoff_image_snapshot cell input input_fd output_fd errors_fd failure
      (Callstate entry_exec_definition[path;arguments;environment]
        (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))suffix))after) /\
    target=dead after.
Proof.
  intros INPUT RUN IMAGE.
  destruct(handoff_guest_image_has_checked_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN IMAGE)
    as[prefix[endpoint[rest[EVENTS[NOIMAGES[PREFIX[SNAPSHOT[TAIL LATER]]]]]]]].
  pose proof SNAPSHOT as SNAP.
  destruct SNAP as[b[after[caller[uidbytes[fdtexts[suffix[SAME[FAILURE FIELDS]]]]]]]];subst endpoint.
  destruct(handoff_exec_image_is_current _ _ _ _ _ _ _ _ _ _ _ _ _ _ FAILURE TAIL LATER)
    as[PATH[ARGUMENTS[ENVIRONMENT[waits[REST TARGET]]]]];subst path arguments environment rest target.
  exists prefix,b,after,caller,suffix,waits;auto 10.
Qed.
