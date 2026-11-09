(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: An actual later image excludes source failure branches. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffEncoding
  NativeHandoffCount NativeHandoffFlags NativeHandoffFormat HandoffRegion NativeHandoffTracePaths.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Definition handoff_trace_failure_safe cell := forall m failure stage error k events target,
  entry_errno_ready cell m -> is_call_cont k ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal EntrySource.f_fail_child)[Vint failure;Vint stage;Vint error]k m))events target ->
  forall path arguments environment,~In(entry_image path arguments environment)events.

Lemma handoff_trace_image_rest events prefix rest path arguments environment :
  events=prefix++rest -> handoff_no_images prefix -> In(entry_image path arguments environment)events ->
  In(entry_image path arguments environment)rest.
Proof.
  intros EVENTS NONE IMAGE;rewrite EVENTS,in_app_iff in IMAGE;destruct IMAGE as[IMPOSSIBLE|IMAGE];[|exact IMAGE].
  unfold handoff_no_images in NONE;rewrite Forall_forall in NONE;specialize(NONE _ IMPOSSIBLE);discriminate.
Qed.

Theorem handoff_trace_count_good cell e le m k bad returned selected count failure events target path arguments environment :
  handoff_trace_failure_safe cell ->
  e!EntrySource._error_number=None -> e!EntrySource._fail_child=None ->
  le!EntrySource._count=Some(Vint count) -> le!EntrySource._failure=Some(Vint failure) ->
  bad<>EntrySource._count -> bad<>EntrySource._failure -> returned<>EntrySource._failure -> selected<>EntrySource._failure ->
  entry_errno_ready cell m ->
  entry_handoff_steps handoff_ge cell(live(State EntrySource.f_guest(handoff_count_program bad returned selected)k e le m))events target ->
  In(entry_image path arguments environment)events -> 0<Int.signed count<32.
Proof.
  intros SAFE ERRORGLOBAL FAILUREGLOBAL COUNT FAILURE BADCOUNT BADFAIL RETURNFAIL SELECTFAIL ERRNO RUN IMAGE.
  pose proof(handoff_count_region cell e le m k bad returned selected count failure(fun _=>True)
    ERRORGLOBAL FAILUREGLOBAL COUNT FAILURE BADCOUNT BADFAIL RETURNFAIL SELECTFAIL ERRNO I)as CERT.
  destruct(handoff_region_image_requires_leaf _ _ _ _ _ _ _ _ _ _ _ CERT RUN IMAGE)
    as[prefix[endpoint[rest[EVENTS[NONE[PREFIX[MEM[LEAF REST]]]]]]]].
  destruct LEAF as[[final[END[FRAME GOOD]]]|[final[error[END[FRAME RANGE]]]]];[exact GOOD|].
  subst endpoint;exfalso;eapply(SAFE m failure Int.one error(Kcall None EntrySource.f_guest e final k)rest target ERRNO I REST).
  eapply handoff_trace_image_rest;eassumption.
Qed.

Theorem handoff_trace_error_failure_no_image cell e le m k returned stage failure events target :
  handoff_trace_failure_safe cell ->
  e!EntrySource._error_number=None -> e!EntrySource._fail_child=None -> returned<>EntrySource._failure ->
  le!EntrySource._failure=Some(Vint failure) -> entry_errno_ready cell m ->
  entry_handoff_steps handoff_ge cell(live(State EntrySource.f_guest(handoff_error_failure_program returned stage)k e le m))events target ->
  forall path arguments environment,~In(entry_image path arguments environment)events.
Proof.
  intros SAFE ERRORGLOBAL FAILUREGLOBAL DIFFERENT FAILURE ERRNO RUN path arguments environment IMAGE.
  pose proof(handoff_error_failure_region cell e le m k returned stage failure(fun _=>True)
    ERRORGLOBAL FAILUREGLOBAL DIFFERENT FAILURE ERRNO I)as CERT.
  destruct(handoff_region_image_requires_leaf _ _ _ _ _ _ _ _ _ _ _ CERT RUN IMAGE)
    as[prefix[endpoint[rest[EVENTS[NONE[PREFIX[MEM[[error[RANGE END]] REST]]]]]]]].
  subst endpoint;eapply(SAFE m failure stage error(Kcall None EntrySource.f_guest e(PTree.set returned(Vint error)le)k)rest target ERRNO I REST).
  eapply handoff_trace_image_rest;eassumption.
Qed.

Theorem handoff_trace_const_failure_no_image cell e le m k failure stage error events target :
  handoff_trace_failure_safe cell -> e!EntrySource._fail_child=None ->
  le!EntrySource._failure=Some(Vint failure) -> entry_errno_ready cell m ->
  entry_handoff_steps handoff_ge cell
    (live(State EntrySource.f_guest
      (Scall None(Evar EntrySource._fail_child(Tfunction[tint;tuint;tint]tvoid cc_default))
        [Etempvar EntrySource._failure tint;Econst_int stage tint;Econst_int error tint])k e le m))events target ->
  forall path arguments environment,~In(entry_image path arguments environment)events.
Proof.
  intros SAFE GLOBAL FAILURE ERRNO RUN path arguments environment IMAGE.
  assert(EDGE:store_edge handoff_ge
    (State EntrySource.f_guest
      (Scall None(Evar EntrySource._fail_child(Tfunction[tint;tuint;tint]tvoid cc_default))
        [Etempvar EntrySource._failure tint;Econst_int stage tint;Econst_int error tint])k e le m)
    (Callstate(Internal EntrySource.f_fail_child)[Vint failure;Vint stage;Vint error]
      (Kcall None EntrySource.f_guest e le k)m)).
  { eapply handoff_failure_call_edge;[exact GLOBAL|exact FAILURE|apply old_expression_value,value_int|reflexivity|apply old_expression_value,value_int|reflexivity]. }
  assert(PATH:store_path handoff_ge(fun _=>True)
    (State EntrySource.f_guest
      (Scall None(Evar EntrySource._fail_child(Tfunction[tint;tuint;tint]tvoid cc_default))
        [Etempvar EntrySource._failure tint;Econst_int stage tint;Econst_int error tint])k e le m)1
    (Callstate(Internal EntrySource.f_fail_child)[Vint failure;Vint stage;Vint error]
      (Kcall None EntrySource.f_guest e le k)m))by(econstructor;[exact I|exact EDGE|constructor;exact I]).
  destruct(handoff_trace_source_split _ _ _ _ _ _ _ _ _ _ _ PATH RUN IMAGE)
    as[prefix[rest[EVENTS[FLAGS[PREFIX[REST AFTER]]]]]].
  eapply(SAFE m failure stage error(Kcall None EntrySource.f_guest e le k)rest target ERRNO I REST);exact AFTER.
Qed.

Theorem handoff_trace_spec_count cell e le m k bad returned selected count failure R wanted :
  handoff_trace_failure_safe cell ->
  e!EntrySource._error_number=None -> e!EntrySource._fail_child=None ->
  le!EntrySource._count=Some(Vint count) -> le!EntrySource._failure=Some(Vint failure) ->
  bad<>EntrySource._count -> bad<>EntrySource._failure -> returned<>EntrySource._failure -> selected<>EntrySource._failure ->
  entry_errno_ready cell m ->
  (0<Int.signed count<32 -> handoff_trace_spec handoff_ge cell R wanted
    (State EntrySource.f_guest Sskip k e(PTree.set bad(Vint Int.zero)le)m)) ->
  handoff_trace_spec handoff_ge cell R wanted(State EntrySource.f_guest(handoff_count_program bad returned selected)k e le m).
Proof.
  intros SAFE ERRORGLOBAL FAILUREGLOBAL COUNT FAILURE BADCOUNT BADFAIL RETURNFAIL SELECTFAIL ERRNO NEXT
    events target path arguments environment RUN IMAGE.
  assert(GOOD:0<Int.signed count<32)
    by(exact(handoff_trace_count_good cell e le m k bad returned selected count failure events target path arguments environment
      SAFE ERRORGLOBAL FAILUREGLOBAL COUNT FAILURE BADCOUNT BADFAIL RETURNFAIL SELECTFAIL ERRNO RUN IMAGE)).
  eapply handoff_trace_cut_source.
  - apply handoff_count_success_source with(count:=count);assumption.
  - exact RUN.
  - exact IMAGE.
  - intros rest REST LATER;exact(NEXT GOOD rest target path arguments environment REST LATER).
Qed.

Theorem handoff_trace_spec_checked_flags cell e le m k code error failure descriptor flags R tail :
  handoff_trace_failure_safe cell ->
  e!EntrySource._error_number=None -> e!EntrySource._fail_child=None ->
  code<>EntrySource._failure -> error<>EntrySource._failure -> le!EntrySource._failure=Some(Vint failure) ->
  (forall after,entry_errno_frame cell m after ->entry_errno_ready cell after ->
    handoff_trace_spec handoff_ge cell R tail
      (State EntrySource.f_guest Sskip k e(PTree.set code(Vint Int.zero)le)after)) ->
  handoff_trace_spec handoff_ge cell R(handoff_flag_event descriptor flags Int.zero::tail)
    (Callstate entry_flags_definition[Vint descriptor;Vint flags]
      (Kcall(Some code)EntrySource.f_guest e le(Kseq(handoff_flags_error code error)k))m).
Proof.
  intros SAFE ERRORGLOBAL FAILUREGLOBAL CODEFAIL ERRORFAIL FAILURE NEXT
    events target path arguments environment RUN IMAGE.
  eapply handoff_trace_cut_flags;[exact RUN|exact IMAGE|].
  intros returned after rest FRAME READY REST LATER.
  pose proof(handoff_flags_return_source e le after k code error returned)as SCRIPT.
  destruct(handoff_trace_source_split _ _ _ _ _ _ _ _ _ _ _ SCRIPT REST LATER)
    as[prefix[remaining[EVENTS[NOFLAGS[PREFIX[TAIL IMAGE']]]]]].
  destruct(Int.eq returned Int.zero)eqn:ZERO.
  - apply Int.same_if_eq in ZERO;subst returned;split;[reflexivity|].
    change(handoff_trace_cut handoff_ge cell R([]++tail)
      (Returnstate(Vint Int.zero)(Kcall(Some code)EntrySource.f_guest e le(Kseq(handoff_flags_error code error)k))after)
      rest target path arguments environment).
    eapply handoff_trace_cut_join;[exact EVENTS|exact NOFLAGS|exact PREFIX|exact(NEXT after FRAME READY remaining target path arguments environment TAIL IMAGE')].
  - exfalso;eapply(handoff_trace_error_failure_no_image cell e(PTree.set code(Vint returned)le)after k error(Int.repr 3)failure
      remaining target SAFE ERRORGLOBAL FAILUREGLOBAL ERRORFAIL).
    + rewrite PTree.gso by congruence;exact FAILURE.
    + exact READY.
    + exact TAIL.
    + exact IMAGE'.
Qed.
