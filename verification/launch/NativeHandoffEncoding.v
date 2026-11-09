(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Real formatter bytes must pass both extent and numeric readback before continuation. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine HandoffRegion
  NativeHandoffStructure NativeHandoffArguments NativeHandoffAllocation NativeHandoffInput
  NativeHandoffNumeric NativeHandoffMemory NativeHandoffFormat NativeHandoffEffects NativeHandoffCount NativeHandoffDescriptors NativeHandoffFlags.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberInitial NumberControl.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Definition handoff_failure_result cell failure state := exists stage error k m,
  state=Callstate (Internal EntrySource.f_fail_child) [Vint failure;Vint stage;Vint error] k m /\
  (stage=Int.one \/ stage=Int.repr 3) /\ 1<=Int.signed error<=4095 /\ entry_errno_ready cell m /\ is_call_cont k.

Lemma handoff_const_failure_region cell e le m k failure stage error R remaining :
  e!EntrySource._fail_child=None -> le!EntrySource._failure=Some(Vint failure) ->
  (stage=Int.one \/ stage=Int.repr 3) -> 1<=Int.signed error<=4095 -> entry_errno_ready cell m ->
  (forall state,handoff_failure_result cell failure state->R state) ->
  handoff_region handoff_ge cell (fun _=>True) R (S remaining)
    (State EntrySource.f_guest
      (Scall None (Evar EntrySource._fail_child(Tfunction [tint;tuint;tint] tvoid cc_default))
        [Etempvar EntrySource._failure tint;Econst_int stage tint;Econst_int error tint]) k e le m).
Proof.
  intros GLOBAL FAILURE STAGE ERROR ERRNO ACCEPT.
  eapply handoff_region_source_prepend; [exact I|eapply handoff_failure_call_edge|].
  - exact GLOBAL.
  - exact FAILURE.
  - apply old_expression_value,value_int.
  - reflexivity.
  - apply old_expression_value,value_int.
  - reflexivity.
  - apply handoff_region_stop; [exact I|]. apply ACCEPT.
    exists stage,error,(Kcall None EntrySource.f_guest e le k),m.
    split;[reflexivity|]. split;[exact STAGE|]. split;[exact ERROR|]. split;[exact ERRNO|exact I].
Qed.

Lemma handoff_uid_format_failure le returned :
  (handoff_format_env EntrySource._t'40 EntrySource._t'3
    (Vint (handoff_borrowed_uid returned)) le Int.zero)!EntrySource._failure=le!EntrySource._failure.
Proof. unfold handoff_format_env; rewrite !PTree.gso by discriminate; reflexivity. Qed.

Lemma handoff_uid_tail6_actual : guest_tail 6 (fn_body EntrySource.f_guest)=
  Ssequence (guest_phase 6) (guest_tail 7 (fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.
Lemma handoff_uid_tail7_actual : guest_tail 7 (fn_body EntrySource.f_guest)=
  Ssequence (guest_phase 7) (guest_tail 8 (fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.
Lemma handoff_uid_tail8_actual : guest_tail 8 (fn_body EntrySource.f_guest)=
  Ssequence (guest_phase 8) (guest_tail 9 (fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.

Theorem handoff_uid_encoding_region cell input b words before le k failure R remaining :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 ->
  le!EntrySource._failure=Some(Vint failure) ->
  (forall state,handoff_failure_result cell failure state->R state) ->
  (forall after final bytes,
    handoff_live_data cell input b words after ->
    final!EntrySource._failure=Some(Vint failure) ->
    number_input after (handoff_uid b) Ptrofs.zero bytes ->
    (1<=length bytes<32)%nat ->
    decimal_number bytes=Some(Int.unsigned(handoff_borrowed_uid input)) ->
    handoff_region handoff_ge cell (fun _=>True) R remaining
      (State EntrySource.f_guest (guest_tail 9 (fn_body EntrySource.f_guest))
        k (handoff_locals_env b) final after)) ->
  handoff_region handoff_ge cell (fun _=>True) R (4000+remaining)
    (State EntrySource.f_guest (guest_tail 6 (fn_body EntrySource.f_guest))
      k (handoff_locals_env b) le before).
Proof.
  intros LAYOUT LIVE UIDBOUND FAILURE ACCEPT NEXT.
  set (wanted:=Int.unsigned(handoff_borrowed_uid input)).
  assert (WANTED:0<=wanted<=Int.max_unsigned) by
    (unfold wanted;apply Int.unsigned_range_2).
  set (k6:=Kseq (guest_tail 7 (fn_body EntrySource.f_guest)) k).
  set (k7:=Kseq (guest_tail 8 (fn_body EntrySource.f_guest)) k).
  set (k8:=Kseq (guest_tail 9 (fn_body EntrySource.f_guest)) k).
  eapply handoff_region_weaken with (n:=(1+5+1+(3+2+128+(2+3215+(1+remaining))))%nat); [|lia].
  rewrite handoff_uid_tail6_actual at 1.
  eapply handoff_region_source_prepend; [exact I|apply unchanged_store_edge;WriteAll.structural|].
  eapply handoff_region_store_path with (count:=5%nat).
  - eapply number_path_implication with (P:=fun after=>after=before); [intros;exact I|].
    apply handoff_uid_format_call_source with (wanted:=wanted).
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + exact(proj1(proj2(handoff_local_bindings b))).
    + unfold wanted;rewrite Int.repr_unsigned;exact(handoff_borrowed_uid_load _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE)).
    + exact WANTED.
  - apply handoff_format_region.
    + exact I.
    + apply handoff_uid_owned;exact(handoff_live_owned _ _ _ _ _ LIVE).
    + exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE)).
    + intros;exact I.
    + intros returned formatted RESULT.
      assert (FORMATTED:handoff_live_data cell input b words formatted)
        by (eapply handoff_live_formatted;[exact LAYOUT|exact LIVE|left;reflexivity|exact RESULT]).
      set (formatle:=handoff_format_env EntrySource._t'40 EntrySource._t'3 (Vint(Int.repr wanted)) le returned).
      assert (FORMATFAILURE:formatle!EntrySource._failure=Some(Vint failure)).
      { unfold formatle,handoff_format_env;rewrite !PTree.gso by discriminate;exact FAILURE. }
      eapply handoff_region_store_path with (count:=3%nat).
      * eapply number_path_implication with (P:=fun after=>after=formatted); [intros;exact I|].
        apply handoff_format_return_source;discriminate.
      * eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
        rewrite handoff_uid_tail7_actual at 1.
        eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
        rewrite handoff_uid_count_actual at 1.
        eapply handoff_region_bind with (n:=128%nat).
        -- apply handoff_count_region with (failure:=failure).
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ unfold formatle,handoff_format_env;apply PTree.gss.
           ++ exact FORMATFAILURE.
           ++ discriminate.
           ++ discriminate.
           ++ discriminate.
           ++ discriminate.
           ++ exact(entry_format_errno _ _ _ _ _ _ RESULT).
           ++ exact I.
        -- intros endpoint [[checked [ENDPOINT [FRAME GOOD]]]|[checked [error [ENDPOINT [FRAME ERROR]]]]];subst endpoint.
           ++ assert (CHECKFAILURE:checked!EntrySource._failure=Some(Vint failure)).
              { rewrite FRAME by (cbn;intuition discriminate);exact FORMATFAILURE. }
              destruct (entry_format_string _ _ _ _ _ _ RESULT GOOD) as [bytes [LENGTH TEXT]].
              assert (BYTES:(1<=length bytes<32)%nat) by lia.
              eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
              rewrite handoff_uid_tail8_actual at 1.
              eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
              assert (UIDLOAD:Mem.loadv Mint32 formatted
                (Vptr(handoff_symbol EntrySource._run_uid)Ptrofs.zero)=Some(Vint(Int.repr wanted))).
              { unfold wanted;rewrite Int.repr_unsigned;exact(handoff_borrowed_uid_load _ _ _ (handoff_live_borrowed _ _ _ _ _ FORMATTED)). }
              assert (UIDENCODED:handoff_uid b<>handoff_encoded b).
              { destruct LAYOUT as [DISTINCT _];cbn[handoff_objects map fst] in DISTINCT.
                repeat match goal with N:NoDup (_::_)|-_=>inversion N;clear N;subst end;cbn in *;intuition congruence. }
              assert (GLOBALENCODED:handoff_symbol EntrySource._run_uid<>handoff_encoded b).
              { destruct (handoff_private_object cell input b (handoff_encoded b) 8 LAYOUT
                  ltac:(unfold handoff_objects;cbn;auto 8)) as [_ SHARED].
                intros SAME;apply SHARED;rewrite <- SAME;apply handoff_borrowed_global_member;cbn;auto. }
              destruct (handoff_uid_numeric_source (handoff_locals_env b) checked formatted k8
                (handoff_uid b) (handoff_encoded b) bytes wanted
                ltac:(exact(proj1(proj2(handoff_local_bindings b))))
                ltac:(unfold handoff_locals_env;WriteAll.lookup)
                ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
                ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
                GLOBALENCODED UIDENCODED UIDLOAD WANTED TEXT
                (handoff_encoded_owned _ _ (handoff_live_owned _ _ _ _ _ FORMATTED)))
                as [count [after [BOUND [POST [AFTERTEXT PATH]]]]].
              assert (AFTERLIVE:handoff_live_data cell input b words after)
                by (eapply handoff_live_number;[exact LAYOUT|exact FORMATTED|exact POST]).
              assert (COUNTBOUND:(count<=3215)%nat) by lia.
              eapply handoff_region_weaken with (n:=(count+(1+remaining))%nat);[|lia].
              eapply handoff_region_store_path with (count:=count).
              ** eapply number_path_implication;[intros;exact I|exact PATH].
              ** destruct (handoff_numeric_bad (decimal_number bytes) wanted) eqn:BAD.
                 --- apply handoff_const_failure_region with (failure:=failure).
                     +++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
                     +++ unfold handoff_numeric_env;destruct(decimal_number bytes);repeat rewrite PTree.gso by discriminate;exact CHECKFAILURE.
                     +++ left;reflexivity.
                     +++ change (1<=71<=4095);lia.
                     +++ exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ AFTERLIVE)).
                     +++ exact ACCEPT.
                 --- eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
                     apply NEXT with (bytes:=bytes).
                     +++ exact AFTERLIVE.
                     +++ unfold handoff_numeric_env;destruct(decimal_number bytes);repeat rewrite PTree.gso by discriminate;exact CHECKFAILURE.
                     +++ exact AFTERTEXT.
                     +++ exact BYTES.
                     +++ apply handoff_numeric_good;exact BAD.
           ++ apply handoff_region_stop;[exact I|]. apply ACCEPT.
              exists Int.one,error,(Kcall None EntrySource.f_guest (handoff_locals_env b) checked k7),formatted;split;[reflexivity|]. split;[left;reflexivity|]. split;[exact ERROR|]. split;[exact(entry_format_errno _ _ _ _ _ _ RESULT)|exact I].
Qed.

Definition handoff_fd_after_count := match handoff_descriptor_after_format with
  | Ssequence _ rest=>rest | _=>Sskip end.
Lemma handoff_fd_after_format_actual : handoff_descriptor_after_format=
  Ssequence handoff_fd_count handoff_fd_after_count.
Proof. reflexivity. Qed.
Lemma handoff_fd_after_count_actual : handoff_fd_after_count=
  Ssequence handoff_fd_numeric handoff_fd_flags.
Proof. reflexivity. Qed.
Lemma handoff_flags_error_actual code error : handoff_flags_error code error=
  Sifthenelse(Etempvar code tint)(handoff_error_failure_program error (Int.repr 3)) Sskip.
Proof. reflexivity. Qed.

Theorem handoff_fd_encoding_region cell input b words before le k failure index R remaining :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  0<=index<4 -> 4<=Int.signed(words index) ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> le!EntrySource._failure=Some(Vint failure) ->
  (forall state,handoff_failure_result cell failure state->R state) ->
  (forall after final bytes,
    handoff_live_data cell input b words after ->
    final!EntrySource._i=Some(Vint(Int.repr index)) -> final!EntrySource._failure=Some(Vint failure) ->
    number_input after (handoff_numbers b) (Ptrofs.repr(32*index)) bytes ->
    (1<=length bytes<32)%nat -> decimal_number bytes=Some(Int.signed(words index)) ->
    handoff_encoding_frame cell b (handoff_numbers b) (Ptrofs.repr(32*index)) before after ->
    handoff_region handoff_ge cell (fun _=>True) R remaining
      (State EntrySource.f_guest Sskip k (handoff_locals_env b) final after)) ->
  handoff_region handoff_ge cell (fun _=>True) R (4500+remaining)
    (State EntrySource.f_guest handoff_fd_format
      (Kseq handoff_descriptor_after_format k) (handoff_locals_env b) le before).
Proof.
  intros LAYOUT LIVE INDEXBOUND POSITIVE INDEX FAILURE ACCEPT NEXT.
  set(wanted:=Int.signed(words index)).
  assert(WANTED:4<=wanted<=Int.max_signed) by (unfold wanted;pose proof(Int.signed_range(words index));lia).
  set(kformat:=Kseq handoff_descriptor_after_format k).
  set(kcount:=Kseq handoff_fd_after_count k).
  set(knumber:=Kseq handoff_fd_flags k).
  eapply handoff_region_weaken with
    (n:=(5+1+(3+2+128+(2+3215+(1+5+1+(3+128+remaining)))))%nat);[|lia].
  eapply handoff_region_store_path with(count:=5%nat).
  - eapply number_path_implication with(P:=fun after=>after=before);[intros;exact I|].
    apply handoff_fd_format_call_source with(handles:=handoff_handles b)(index:=index)(wanted:=wanted).
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + unfold handoff_locals_env;WriteAll.lookup.
    + unfold handoff_locals_env;WriteAll.lookup.
    + exact INDEX.
    + exact INDEXBOUND.
    + unfold wanted;rewrite Int.repr_signed;exact(handoff_live_handles _ _ _ _ _ LIVE _ INDEXBOUND).
    + exact WANTED.
  - apply handoff_format_region.
    + exact I.
    + apply handoff_numbers_owned;[exact(handoff_live_owned _ _ _ _ _ LIVE)|exact INDEXBOUND].
    + exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE)).
    + intros;exact I.
    + intros returned formatted RESULT.
      assert(FORMATTED:handoff_live_data cell input b words formatted)
        by(eapply handoff_live_formatted;[exact LAYOUT|exact LIVE|right;reflexivity|exact RESULT]).
      set(formatle:=handoff_format_env EntrySource._t'34 EntrySource._t'9(Vint(Int.repr wanted)) le returned).
      assert(FORMATINDEX:formatle!EntrySource._i=Some(Vint(Int.repr index))).
      { unfold formatle,handoff_format_env;rewrite !PTree.gso by discriminate;exact INDEX. }
      assert(FORMATFAILURE:formatle!EntrySource._failure=Some(Vint failure)).
      { unfold formatle,handoff_format_env;rewrite !PTree.gso by discriminate;exact FAILURE. }
      eapply handoff_region_store_path with(count:=3%nat).
      * eapply number_path_implication with(P:=fun after=>after=formatted);[intros;exact I|].
        apply handoff_format_return_source;discriminate.
      * eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
        rewrite handoff_fd_after_format_actual at 1.
        eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
        rewrite handoff_fd_count_actual at 1.
        eapply handoff_region_bind with(n:=128%nat).
        -- apply handoff_count_region with(failure:=failure).
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ unfold formatle,handoff_format_env;apply PTree.gss.
           ++ exact FORMATFAILURE.
           ++ discriminate.
           ++ discriminate.
           ++ discriminate.
           ++ discriminate.
           ++ exact(entry_format_errno _ _ _ _ _ _ RESULT).
           ++ exact I.
        -- intros endpoint [[checked [ENDPOINT [FRAME GOOD]]]|[checked [error [ENDPOINT [FRAME ERROR]]]]];subst endpoint.
           ++ assert(CHECKINDEX:checked!EntrySource._i=Some(Vint(Int.repr index))).
              { rewrite FRAME by(cbn;intuition discriminate);exact FORMATINDEX. }
              assert(CHECKFAILURE:checked!EntrySource._failure=Some(Vint failure)).
              { rewrite FRAME by(cbn;intuition discriminate);exact FORMATFAILURE. }
              destruct(entry_format_string _ _ _ _ _ _ RESULT GOOD) as[bytes[LENGTH TEXT]].
              assert(BYTES:(1<=length bytes<32)%nat) by lia.
              eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
              rewrite handoff_fd_after_count_actual at 1.
              eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
              destruct(handoff_uid_numbers_separate b(proj1 LAYOUT)) as[UIDNUM[UIDENC NUMENC]].
              assert(HANDLEENC:handoff_handles b<>handoff_encoded b)
                by(apply handoff_local_handles_other;[exact(proj1 LAYOUT)|tauto]).
              assert(HANDLELOAD:Mem.loadv Mint32 formatted(Vptr(handoff_handles b)(Ptrofs.repr(4*index)))=
                Some(Vint(Int.repr wanted))).
              { unfold wanted;rewrite Int.repr_signed;exact(handoff_live_handles _ _ _ _ _ FORMATTED _ INDEXBOUND). }
              destruct(handoff_fd_numeric_source (handoff_locals_env b) checked formatted knumber
                (handoff_numbers b)(handoff_encoded b)(handoff_handles b) index bytes wanted
                ltac:(unfold handoff_locals_env;WriteAll.lookup)
                ltac:(unfold handoff_locals_env;WriteAll.lookup)
                ltac:(unfold handoff_locals_env;WriteAll.lookup)
                ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
                HANDLEENC NUMENC CHECKINDEX INDEXBOUND HANDLELOAD WANTED TEXT
                (handoff_encoded_owned _ _ (handoff_live_owned _ _ _ _ _ FORMATTED)))
                as[count[numbered[BOUND[POST[NUMBERTEXT PATH]]]]].
              assert(NUMBERED:handoff_live_data cell input b words numbered)
                by(eapply handoff_live_number;[exact LAYOUT|exact FORMATTED|exact POST]).
              assert(COUNTBOUND:(count<=3215)%nat) by lia.
              set(numberle:=handoff_numeric_env EntrySource._t'13 EntrySource._t'14 EntrySource._t'32 EntrySource._t'33
                checked(decimal_number bytes)wanted(Vint(Int.repr wanted))).
              assert(NUMBERINDEX:numberle!EntrySource._i=Some(Vint(Int.repr index))).
              { unfold numberle,handoff_numeric_env;destruct(decimal_number bytes);repeat rewrite PTree.gso by discriminate;exact CHECKINDEX. }
              assert(NUMBERFAILURE:numberle!EntrySource._failure=Some(Vint failure)).
              { unfold numberle,handoff_numeric_env;destruct(decimal_number bytes);repeat rewrite PTree.gso by discriminate;exact CHECKFAILURE. }
              eapply handoff_region_weaken with(n:=(count+(1+5+1+(3+128+remaining)))%nat);[|lia].
              eapply handoff_region_store_path with(count:=count).
              ** eapply number_path_implication;[intros;exact I|exact PATH].
              ** destruct(handoff_numeric_bad(decimal_number bytes)wanted) eqn:BAD.
                 --- apply handoff_const_failure_region with(failure:=failure).
                     +++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
                     +++ exact NUMBERFAILURE.
                     +++ left;reflexivity.
                     +++ change(1<=71<=4095);lia.
                     +++ exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ NUMBERED)).
                     +++ exact ACCEPT.
                 --- eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
                     eapply handoff_region_store_path with(count:=5%nat).
                     +++ eapply number_path_implication with(P:=fun after=>after=numbered);[intros;exact I|].
                         apply handoff_fd_flags_call_source with(handles:=handoff_handles b)(index:=index).
                         *** apply handoff_nonlocal_binding;cbn;intuition discriminate.
                         *** unfold handoff_locals_env;WriteAll.lookup.
                         *** exact NUMBERINDEX.
                         *** exact INDEXBOUND.
                         *** exact(handoff_live_handles _ _ _ _ _ NUMBERED _ INDEXBOUND).
                     +++ apply handoff_flags_region.
                         *** exact I.
                         *** exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ NUMBERED)).
                         *** intros;exact I.
                         *** intros flag_return flags_after FLAGFRAME FLAGERRNO.
                             assert(FLAGGED:handoff_live_data cell input b words flags_after)
                               by(eapply handoff_live_errno_returned;[exact LAYOUT|exact NUMBERED|exact FLAGFRAME|exact FLAGERRNO]).
                             set(flagle:=PTree.set EntrySource._t'16(Vint flag_return)
                               (PTree.set EntrySource._t'31(Vint(words index)) numberle)).
                             assert(FLAGINDEX:flagle!EntrySource._i=Some(Vint(Int.repr index))).
                             { unfold flagle;rewrite !PTree.gso by discriminate;exact NUMBERINDEX. }
                             assert(FLAGFAILURE:flagle!EntrySource._failure=Some(Vint failure)).
                             { unfold flagle;rewrite !PTree.gso by discriminate;exact NUMBERFAILURE. }
                             unfold handoff_flags_fd_cont.
                             eapply handoff_region_store_path with(count:=3%nat).
                             ---- eapply number_path_implication with(P:=fun after=>after=flags_after);[intros;exact I|].
                                  apply handoff_flags_return_source.
                             ---- destruct(Int.eq flag_return Int.zero) eqn:ZERO.
                                  ++++ eapply handoff_region_weaken with(n:=remaining);[|lia].
                                       apply NEXT with(bytes:=bytes).
                                       **** exact FLAGGED.
                                       **** exact FLAGINDEX.
                                       **** exact FLAGFAILURE.
                                       **** eapply handoff_errno_preserves_input;[exact FLAGFRAME| |exact NUMBERTEXT].
                                            exact(proj1(handoff_private_object cell input b(handoff_numbers b)128 LAYOUT
                                              ltac:(unfold handoff_objects;cbn;auto 8))).
                                       **** exact BYTES.
                                       **** apply handoff_numeric_good;exact BAD.
                                       **** eapply handoff_encoding_frame_trans.
                                            ----- eapply handoff_encoding_formatted;exact RESULT.
                                            ----- eapply handoff_encoding_frame_trans.
                                                  +++++ eapply handoff_encoding_number;exact POST.
                                                  +++++ eapply handoff_encoding_errno;exact FLAGFRAME.
                                  ++++ change(handoff_region handoff_ge cell(fun _=>True) R (128+remaining)
                                         (State EntrySource.f_guest (handoff_error_failure_program EntrySource._t'15(Int.repr 3))
                                           k(handoff_locals_env b) flagle flags_after)).
                                       eapply handoff_region_bind with(n:=128%nat).
                                       **** apply handoff_error_failure_region with(failure:=failure).
                                            ----- apply handoff_nonlocal_binding;cbn;intuition discriminate.
                                            ----- apply handoff_nonlocal_binding;cbn;intuition discriminate.
                                            ----- discriminate.
                                            ----- exact FLAGFAILURE.
                                            ----- exact FLAGERRNO.
                                            ----- exact I.
                                       **** intros endpoint [error[ERROR ENDPOINT]];subst endpoint.
                                            apply handoff_region_stop;[exact I|]. apply ACCEPT.
                                            exists(Int.repr 3),error,
                                              (Kcall None EntrySource.f_guest(handoff_locals_env b)
                                                (PTree.set EntrySource._t'15(Vint error)flagle) k),flags_after.
                                            split;[reflexivity|]. split;[right;reflexivity|]. split;[exact ERROR|]. split;[exact FLAGERRNO|exact I].
           ++ apply handoff_region_stop;[exact I|]. apply ACCEPT.
              exists Int.one,error,(Kcall None EntrySource.f_guest(handoff_locals_env b)checked kcount),formatted.
              split;[reflexivity|]. split;[left;reflexivity|]. split;[exact ERROR|]. split;[exact(entry_format_errno _ _ _ _ _ _ RESULT)|exact I].
Qed.
