(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Descriptor flag observations are extracted from the actual encoding run. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffNumeric NativeHandoffMemory NativeHandoffFormat
  NativeHandoffEncoding NativeHandoffDescriptors NativeHandoffFlags NativeHandoffCount
  NativeHandoffTracePaths NativeHandoffTraceChecks.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberInitial NumberControl.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.
Ltac handoff_trace_route := eapply handoff_trace_spec_edge;[apply unchanged_store_edge;WriteAll.structural|].

Theorem handoff_trace_uid cell input b words before le k failure R trace :
  handoff_trace_failure_safe cell ->
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 -> le!EntrySource._failure=Some(Vint failure) ->
  (forall after final,handoff_live_data cell input b words after -> final!EntrySource._failure=Some(Vint failure) ->
    handoff_trace_spec handoff_ge cell R trace
      (State EntrySource.f_guest(guest_tail 9(fn_body EntrySource.f_guest))k(handoff_locals_env b)final after)) ->
  handoff_trace_spec handoff_ge cell R trace
    (State EntrySource.f_guest(guest_tail 6(fn_body EntrySource.f_guest))k(handoff_locals_env b)le before).
Proof.
  intros SAFE LAYOUT LIVE UIDBOUND FAILURE NEXT.
  set(wanted:=Int.unsigned(handoff_borrowed_uid input)).
  assert(WANTED:0<=wanted<=Int.max_unsigned)by(unfold wanted;apply Int.unsigned_range_2).
  set(k6:=Kseq(guest_tail 7(fn_body EntrySource.f_guest))k).
  set(k7:=Kseq(guest_tail 8(fn_body EntrySource.f_guest))k).
  set(k8:=Kseq(guest_tail 9(fn_body EntrySource.f_guest))k).
  rewrite handoff_uid_tail6_actual at 1;handoff_trace_route.
  eapply handoff_trace_spec_source.
  - apply handoff_uid_format_call_source with(wanted:=wanted).
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + exact(proj1(proj2(handoff_local_bindings b))).
    + unfold wanted;rewrite Int.repr_unsigned;exact(handoff_borrowed_uid_load _ _ _(handoff_live_borrowed _ _ _ _ _ LIVE)).
    + exact WANTED.
  - apply handoff_trace_spec_format;intros returned formatted RESULT.
    assert(FORMATTED:handoff_live_data cell input b words formatted)
      by(eapply handoff_live_formatted;[exact LAYOUT|exact LIVE|left;reflexivity|exact RESULT]).
    set(formatle:=handoff_format_env EntrySource._t'40 EntrySource._t'3(Vint(Int.repr wanted))le returned).
    assert(FORMATFAILURE:formatle!EntrySource._failure=Some(Vint failure)).
    { unfold formatle,handoff_format_env;rewrite !PTree.gso by discriminate;exact FAILURE. }
    eapply handoff_trace_spec_source;[apply handoff_format_return_source;discriminate|].
    handoff_trace_route;rewrite handoff_uid_tail7_actual at 1;handoff_trace_route.
    rewrite handoff_uid_count_actual at 1.
    eapply handoff_trace_spec_count with(failure:=failure)(count:=returned).
    + exact SAFE.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + unfold formatle,handoff_format_env;apply PTree.gss.
    + exact FORMATFAILURE.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + exact(entry_format_errno _ _ _ _ _ _ RESULT).
    + intros GOOD;set(checked:=PTree.set EntrySource._t'6(Vint Int.zero)formatle).
      assert(CHECKFAILURE:checked!EntrySource._failure=Some(Vint failure)).
      { unfold checked;rewrite PTree.gso by discriminate;exact FORMATFAILURE. }
      destruct(entry_format_string _ _ _ _ _ _ RESULT GOOD)as[bytes[LENGTH TEXT]].
      handoff_trace_route;rewrite handoff_uid_tail8_actual at 1;handoff_trace_route.
      assert(UIDLOAD:Mem.loadv Mint32 formatted(Vptr(handoff_symbol EntrySource._run_uid)Ptrofs.zero)=Some(Vint(Int.repr wanted))).
      { unfold wanted;rewrite Int.repr_unsigned;exact(handoff_borrowed_uid_load _ _ _(handoff_live_borrowed _ _ _ _ _ FORMATTED)). }
      assert(UIDENCODED:handoff_uid b<>handoff_encoded b).
      { destruct LAYOUT as[DISTINCT _];cbn[handoff_objects map fst]in DISTINCT.
        repeat match goal with N:NoDup(_::_)|-_=>inversion N;clear N;subst end;cbn in *;intuition congruence. }
      assert(GLOBALENCODED:handoff_symbol EntrySource._run_uid<>handoff_encoded b).
      { destruct(handoff_private_object cell input b(handoff_encoded b)8 LAYOUT
          ltac:(unfold handoff_objects;cbn;auto 8))as[_ SHARED].
        intros SAME;apply SHARED;rewrite <- SAME;apply handoff_borrowed_global_member;cbn;auto. }
      destruct(handoff_uid_numeric_source(handoff_locals_env b)checked formatted k8
        (handoff_uid b)(handoff_encoded b)bytes wanted
        ltac:(exact(proj1(proj2(handoff_local_bindings b))))
        ltac:(unfold handoff_locals_env;WriteAll.lookup)
        ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
        ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
        GLOBALENCODED UIDENCODED UIDLOAD WANTED TEXT
        (handoff_encoded_owned _ _(handoff_live_owned _ _ _ _ _ FORMATTED)))
        as[count[after[BOUND[POST[AFTERTEXT PATH]]]]].
      assert(AFTERLIVE:handoff_live_data cell input b words after)
        by(eapply handoff_live_number;[exact LAYOUT|exact FORMATTED|exact POST]).
      eapply handoff_trace_spec_source;[exact PATH|].
      destruct(handoff_numeric_bad(decimal_number bytes)wanted)eqn:BAD.
      * intros events target path arguments environment RUN IMAGE;exfalso.
        eapply(handoff_trace_const_failure_no_image cell(handoff_locals_env b)(handoff_numeric_env EntrySource._t'7 EntrySource._t'8 EntrySource._t'38 EntrySource._t'39 checked(decimal_number bytes)wanted(Vint(Int.repr wanted)))after k8 failure Int.one(Int.repr 71)events target).
        -- exact SAFE.
        -- apply handoff_nonlocal_binding;cbn;intuition discriminate.
        -- unfold handoff_numeric_env;destruct(decimal_number bytes);repeat rewrite PTree.gso by discriminate;exact CHECKFAILURE.
        -- exact(handoff_borrowed_errno _ _ _(handoff_live_borrowed _ _ _ _ _ AFTERLIVE)).
        -- exact RUN.
        -- exact IMAGE.
      * handoff_trace_route;apply NEXT;[exact AFTERLIVE|].
        unfold handoff_numeric_env;destruct(decimal_number bytes);repeat rewrite PTree.gso by discriminate;exact CHECKFAILURE.
Qed.

Theorem handoff_trace_fd cell input b words before le k failure index R tail :
  handoff_trace_failure_safe cell ->
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  0<=index<4 -> 4<=Int.signed(words index) ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> le!EntrySource._failure=Some(Vint failure) ->
  (forall after final,handoff_live_data cell input b words after ->
    final!EntrySource._i=Some(Vint(Int.repr index)) -> final!EntrySource._failure=Some(Vint failure) ->
    handoff_trace_spec handoff_ge cell R tail(State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)) ->
  handoff_trace_spec handoff_ge cell R(handoff_flag_event(words index)Int.zero Int.zero::tail)
    (State EntrySource.f_guest handoff_fd_format(Kseq handoff_descriptor_after_format k)(handoff_locals_env b)le before).
Proof.
  intros SAFE LAYOUT LIVE INDEXBOUND POSITIVE INDEX FAILURE NEXT.
  set(wanted:=Int.signed(words index)).
  assert(WANTED:4<=wanted<=Int.max_signed)by(unfold wanted;pose proof(Int.signed_range(words index));lia).
  set(kformat:=Kseq handoff_descriptor_after_format k).
  set(kcount:=Kseq handoff_fd_after_count k).
  set(knumber:=Kseq handoff_fd_flags k).
  eapply handoff_trace_spec_source.
  - apply handoff_fd_format_call_source with(handles:=handoff_handles b)(index:=index)(wanted:=wanted).
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + unfold handoff_locals_env;WriteAll.lookup.
    + unfold handoff_locals_env;WriteAll.lookup.
    + exact INDEX.
    + exact INDEXBOUND.
    + unfold wanted;rewrite Int.repr_signed;exact(handoff_live_handles _ _ _ _ _ LIVE _ INDEXBOUND).
    + exact WANTED.
  - apply handoff_trace_spec_format;intros returned formatted RESULT.
    assert(FORMATTED:handoff_live_data cell input b words formatted)
      by(eapply handoff_live_formatted;[exact LAYOUT|exact LIVE|right;reflexivity|exact RESULT]).
    set(formatle:=handoff_format_env EntrySource._t'34 EntrySource._t'9(Vint(Int.repr wanted))le returned).
    assert(FORMATINDEX:formatle!EntrySource._i=Some(Vint(Int.repr index))).
    { unfold formatle,handoff_format_env;rewrite !PTree.gso by discriminate;exact INDEX. }
    assert(FORMATFAILURE:formatle!EntrySource._failure=Some(Vint failure)).
    { unfold formatle,handoff_format_env;rewrite !PTree.gso by discriminate;exact FAILURE. }
    eapply handoff_trace_spec_source;[apply handoff_format_return_source;discriminate|].
    handoff_trace_route;rewrite handoff_fd_after_format_actual at 1;handoff_trace_route.
    rewrite handoff_fd_count_actual at 1.
    eapply handoff_trace_spec_count with(failure:=failure)(count:=returned).
    + exact SAFE.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + unfold formatle,handoff_format_env;apply PTree.gss.
    + exact FORMATFAILURE.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + exact(entry_format_errno _ _ _ _ _ _ RESULT).
    + intros GOOD;set(checked:=PTree.set EntrySource._t'12(Vint Int.zero)formatle).
      assert(CHECKINDEX:checked!EntrySource._i=Some(Vint(Int.repr index))).
      { unfold checked;rewrite PTree.gso by discriminate;exact FORMATINDEX. }
      assert(CHECKFAILURE:checked!EntrySource._failure=Some(Vint failure)).
      { unfold checked;rewrite PTree.gso by discriminate;exact FORMATFAILURE. }
      destruct(entry_format_string _ _ _ _ _ _ RESULT GOOD)as[bytes[LENGTH TEXT]].
      handoff_trace_route;rewrite handoff_fd_after_count_actual at 1;handoff_trace_route.
      destruct(handoff_uid_numbers_separate b(proj1 LAYOUT))as[UIDNUM[UIDENC NUMENC]].
      assert(HANDLEENC:handoff_handles b<>handoff_encoded b)
        by(apply handoff_local_handles_other;[exact(proj1 LAYOUT)|tauto]).
      assert(HANDLELOAD:Mem.loadv Mint32 formatted(Vptr(handoff_handles b)(Ptrofs.repr(4*index)))=Some(Vint(Int.repr wanted))).
      { unfold wanted;rewrite Int.repr_signed;exact(handoff_live_handles _ _ _ _ _ FORMATTED _ INDEXBOUND). }
      destruct(handoff_fd_numeric_source(handoff_locals_env b)checked formatted knumber
        (handoff_numbers b)(handoff_encoded b)(handoff_handles b)index bytes wanted
        ltac:(unfold handoff_locals_env;WriteAll.lookup)ltac:(unfold handoff_locals_env;WriteAll.lookup)
        ltac:(unfold handoff_locals_env;WriteAll.lookup)ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
        HANDLEENC NUMENC CHECKINDEX INDEXBOUND HANDLELOAD WANTED TEXT
        (handoff_encoded_owned _ _(handoff_live_owned _ _ _ _ _ FORMATTED)))
        as[count[numbered[BOUND[POST[NUMBERTEXT PATH]]]]].
      assert(NUMBERED:handoff_live_data cell input b words numbered)
        by(eapply handoff_live_number;[exact LAYOUT|exact FORMATTED|exact POST]).
      set(numberle:=handoff_numeric_env EntrySource._t'13 EntrySource._t'14 EntrySource._t'32 EntrySource._t'33
        checked(decimal_number bytes)wanted(Vint(Int.repr wanted))).
      assert(NUMBERINDEX:numberle!EntrySource._i=Some(Vint(Int.repr index))).
      { unfold numberle,handoff_numeric_env;destruct(decimal_number bytes);repeat rewrite PTree.gso by discriminate;exact CHECKINDEX. }
      assert(NUMBERFAILURE:numberle!EntrySource._failure=Some(Vint failure)).
      { unfold numberle,handoff_numeric_env;destruct(decimal_number bytes);repeat rewrite PTree.gso by discriminate;exact CHECKFAILURE. }
      eapply handoff_trace_spec_source;[exact PATH|].
      destruct(handoff_numeric_bad(decimal_number bytes)wanted)eqn:BAD.
      * intros events target path arguments environment RUN IMAGE;exfalso.
        eapply(handoff_trace_const_failure_no_image cell(handoff_locals_env b)numberle numbered knumber failure Int.one(Int.repr 71)events target).
        -- exact SAFE.
        -- apply handoff_nonlocal_binding;cbn;intuition discriminate.
        -- exact NUMBERFAILURE.
        -- exact(handoff_borrowed_errno _ _ _(handoff_live_borrowed _ _ _ _ _ NUMBERED)).
        -- exact RUN.
        -- exact IMAGE.
      * handoff_trace_route;eapply handoff_trace_spec_source.
        -- apply handoff_fd_flags_call_source with(handles:=handoff_handles b)(index:=index).
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ unfold handoff_locals_env;WriteAll.lookup.
           ++ exact NUMBERINDEX.
           ++ exact INDEXBOUND.
           ++ exact(handoff_live_handles _ _ _ _ _ NUMBERED _ INDEXBOUND).
        -- unfold handoff_flags_fd_cont;apply handoff_trace_spec_checked_flags with(failure:=failure).
           ++ exact SAFE.
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ discriminate.
           ++ discriminate.
           ++ rewrite PTree.gso by discriminate;exact NUMBERFAILURE.
           ++ intros after FRAME READY;apply NEXT.
              ** eapply handoff_live_errno_returned;[exact LAYOUT|exact NUMBERED|exact FRAME|exact READY].
              ** rewrite !PTree.gso by discriminate;exact NUMBERINDEX.
              ** rewrite !PTree.gso by discriminate;exact NUMBERFAILURE.
Qed.
