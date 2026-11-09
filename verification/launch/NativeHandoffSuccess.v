(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Honest primitive outcomes execute the actual checked source path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess LibraryMachine ErrorNumber WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffPaths NativeHandoffStructure
  NativeHandoffArguments NativeHandoffAllocation NativeHandoffInput NativeHandoffMemory NativeHandoffNumeric
  NativeHandoffFormat NativeHandoffCount NativeHandoffEncoding NativeHandoffWitness NativeHandoffDescriptors NativeHandoffFlags.
From LeanCageMainNumber Require Import NumberMemory NumberMath NumberStorage.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Lemma handoff_success_trans ge cell first events middle rest last :
  entry_handoff_steps ge cell first events middle -> entry_handoff_steps ge cell middle rest last ->
  entry_handoff_steps ge cell first(events++rest)last.
Proof. intros FIRST SECOND;induction FIRST;cbn;[exact SECOND|econstructor;eauto]. Qed.
Lemma handoff_success_edge ge cell first middle events last :
  store_edge ge first middle -> entry_handoff_steps ge cell(live middle)events last ->
  entry_handoff_steps ge cell(live first)(handoff_source_event::events)last.
Proof.
  intros[IN[STEP UNIQUE]]TAIL;econstructor;[|exact TAIL].
  apply entry_library_step,original_step,internal;assumption.
Qed.
Lemma handoff_success_path ge cell P first count middle events last :
  store_path ge P first count middle -> entry_handoff_steps ge cell(live middle)events last ->
  entry_handoff_steps ge cell(live first)(repeat handoff_source_event count++events)last.
Proof.
  intros PATH TAIL;induction PATH;cbn;[exact TAIL|eapply handoff_success_edge;eauto].
Qed.
Ltac handoff_success_route := eapply handoff_success_edge;[apply unchanged_store_edge;WriteAll.structural|].

Theorem handoff_uid_success cell input b words before le k failure bytes :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  le!EntrySource._failure=Some(Vint failure) ->
  (1<=length bytes<32)%nat -> Forall(fun byte=>byte<>Byte.zero)bytes ->
  decimal_number bytes=Some(Int.unsigned(handoff_borrowed_uid input)) ->
  exists after final events,
    handoff_live_data cell input b words after /\ final!EntrySource._failure=Some(Vint failure) /\
    number_input after(handoff_uid b)Ptrofs.zero bytes /\
    entry_handoff_steps handoff_ge cell
      (live(State EntrySource.f_guest(guest_tail 6(fn_body EntrySource.f_guest))k(handoff_locals_env b)le before))events
      (live(State EntrySource.f_guest(guest_tail 9(fn_body EntrySource.f_guest))k(handoff_locals_env b)final after)).
Proof.
  intros LAYOUT LIVE FAILURE LENGTH NONZERO PARSED.
  set(wanted:=Int.unsigned(handoff_borrowed_uid input)).
  set(returned:=Int.repr(Z.of_nat(length bytes))).
  assert(GOOD:0<Int.signed returned<32).
  { unfold returned;rewrite Int.signed_repr;[lia|change Int.min_signed with(-2147483648);change Int.max_signed with 2147483647;lia]. }
  destruct(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE))as[error ERRNO].
  destruct(handoff_format_bytes_witness cell before(handoff_uid b)Ptrofs.zero error bytes
    (handoff_uid_owned _ _ (handoff_live_owned _ _ _ _ _ LIVE))ERRNO
    (proj1(handoff_private_object cell input b(handoff_uid b)32 LAYOUT ltac:(unfold handoff_objects;cbn;auto 8)))
    ltac:(lia)NONZERO)as[formatted[STORE[TEXT[ERRNOAFTER RESULT]]]].
  assert(FORMATTED:handoff_live_data cell input b words formatted)
    by(eapply handoff_live_formatted;[exact LAYOUT|exact LIVE|left;reflexivity|exact RESULT]).
  set(formatle:=handoff_format_env EntrySource._t'40 EntrySource._t'3(Vint(Int.repr wanted))le returned).
  set(checked:=PTree.set EntrySource._t'6(Vint Int.zero)formatle).
  assert(WANTED:0<=wanted<=Int.max_unsigned)by(unfold wanted;apply Int.unsigned_range_2).
  assert(UIDLOAD:Mem.loadv Mint32 formatted(Vptr(handoff_symbol EntrySource._run_uid)Ptrofs.zero)=Some(Vint(Int.repr wanted))).
  { unfold wanted;rewrite Int.repr_unsigned;exact(handoff_borrowed_uid_load _ _ _ (handoff_live_borrowed _ _ _ _ _ FORMATTED)). }
  destruct(handoff_uid_numbers_separate b(proj1 LAYOUT))as[UIDNUM[UIDENC NUMENC]].
  assert(GLOBALENC:handoff_symbol EntrySource._run_uid<>handoff_encoded b).
  { destruct(handoff_private_object cell input b(handoff_encoded b)8 LAYOUT
      ltac:(unfold handoff_objects;cbn;auto 8))as[_ SHARED].
    intros SAME;apply SHARED;rewrite <- SAME;apply handoff_borrowed_global_member;cbn;auto. }
  destruct(handoff_uid_numeric_source(handoff_locals_env b)checked formatted
    (Kseq(guest_tail 9(fn_body EntrySource.f_guest))k)(handoff_uid b)(handoff_encoded b)bytes wanted
    ltac:(unfold handoff_locals_env;WriteAll.lookup)ltac:(unfold handoff_locals_env;WriteAll.lookup)
    ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
    ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
    GLOBALENC UIDENC UIDLOAD WANTED TEXT(handoff_encoded_owned _ _ (handoff_live_owned _ _ _ _ _ FORMATTED)))
    as[count[after[BOUND[POST[AFTERTEXT NUMBERPATH]]]]].
  assert(AFTER:handoff_live_data cell input b words after)
    by(eapply handoff_live_number;[exact LAYOUT|exact FORMATTED|exact POST]).
  assert(BAD:handoff_numeric_bad(decimal_number bytes)wanted=false)by(apply handoff_numeric_good;exact PARSED).
  rewrite BAD in NUMBERPATH.
  set(final:=handoff_numeric_env EntrySource._t'7 EntrySource._t'8 EntrySource._t'38 EntrySource._t'39
    checked(decimal_number bytes)wanted(Vint(Int.repr wanted))).
  exists after,final;eexists;split;[exact AFTER|]. split.
  - unfold final,handoff_numeric_env;rewrite PARSED;unfold checked,formatle,handoff_format_env;
      repeat rewrite PTree.gso by discriminate;exact FAILURE.
  - split;[exact AFTERTEXT|]. rewrite handoff_uid_tail6_actual at 1;handoff_success_route.
    eapply handoff_success_path.
    + apply handoff_uid_format_call_source with(wanted:=wanted).
      * apply handoff_nonlocal_binding;cbn;intuition discriminate.
      * apply handoff_nonlocal_binding;cbn;intuition discriminate.
      * unfold handoff_locals_env;WriteAll.lookup.
      * unfold wanted;rewrite Int.repr_unsigned;exact(handoff_borrowed_uid_load _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE)).
      * exact WANTED.
    + econstructor.
      * apply entry_format_step;[apply handoff_uid_owned;exact(handoff_live_owned _ _ _ _ _ LIVE)|exact RESULT].
      * eapply handoff_success_path.
        -- apply handoff_format_return_source;discriminate.
        -- handoff_success_route;rewrite handoff_uid_tail7_actual at 1;handoff_success_route.
           rewrite handoff_uid_count_actual at 1;eapply handoff_success_path.
           ++ apply handoff_count_success_source with(count:=returned).
              ** unfold formatle,handoff_format_env;apply PTree.gss.
              ** exact GOOD.
           ++ handoff_success_route;rewrite handoff_uid_tail8_actual at 1;handoff_success_route.
              eapply handoff_success_path;[exact NUMBERPATH|]. handoff_success_route;constructor.
Qed.

Theorem handoff_alias_success e m handles words index : forall remaining checked le k,
  e!EntrySource._handles=Some(handles,tarray tint 4) ->
  0<=checked -> checked+Z.of_nat remaining=index -> index<4 ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> le!EntrySource._j=Some(Vint(Int.repr checked)) ->
  (forall slot,0<=slot<4 -> Mem.loadv Mint32 m(Vptr handles(Ptrofs.repr(4*slot)))=Some(Vint(words slot))) ->
  (forall slot,checked<=slot<index -> Int.eq(words index)(words slot)=false) ->
  exists count final,
    handoff_alias_temp_frame le final /\
    store_path handoff_ge(fun after=>after=m)
      (State EntrySource.f_guest handoff_descriptor_alias_loop k e le m)count
      (State EntrySource.f_guest Sskip k e final m).
Proof.
  induction remaining as[|remaining IH];intros checked le k LOCAL LOW END HIGH INDEX CHECKED LOADS DISTINCT.
  - cbn[Z.of_nat]in END;assert(checked=index)by lia;subst checked.
    exists 5%nat,le;split;[intros id J LEFT RIGHT;reflexivity|].
    rewrite handoff_alias_loop_actual at 1;handoff_route;rewrite handoff_alias_body_actual at 1;handoff_route.
    eapply store_next;[reflexivity|apply handoff_alias_test_edge with(index:=index)(checked:=index);[exact INDEX|exact CHECKED|lia]|].
    rewrite Z.ltb_irrefl;handoff_route;handoff_route;apply store_done;reflexivity.
  - assert(ORDER:0<=checked<index)by(rewrite Nat2Z.inj_succ in END;lia).
    pose proof(handoff_alias_iteration_source e le m k handles index checked(words index)(words checked)
      LOCAL INDEX CHECKED ORDER HIGH(LOADS index ltac:(lia))(LOADS checked ltac:(lia)))as ITERATION.
    rewrite(DISTINCT checked ltac:(lia))in ITERATION.
    set(next:=PTree.set EntrySource._j(Vint(Int.repr(checked+1)))(handoff_alias_env le(words index)(words checked))).
    assert(NEXTINDEX:next!EntrySource._i=Some(Vint(Int.repr index))).
    { unfold next;rewrite PTree.gso by discriminate;rewrite handoff_alias_env_preserved by discriminate;exact INDEX. }
    destruct(IH(checked+1)next k LOCAL ltac:(lia)ltac:(rewrite Nat2Z.inj_succ in END;lia) HIGH NEXTINDEX
      ltac:(unfold next;apply PTree.gss)LOADS ltac:(intros;apply DISTINCT;lia))as[count[final[FRAME PATH]]].
    exists(14+count)%nat,final;split.
    + intros id J LEFT RIGHT;rewrite FRAME by assumption;unfold next;rewrite PTree.gso by congruence.
      apply handoff_alias_env_preserved;assumption.
    + eapply store_path_trans with(n:=11%nat);[exact ITERATION|].
      eapply store_path_trans with(n:=3%nat)(b:=State EntrySource.f_guest handoff_descriptor_alias_loop k e next m).
      * handoff_route;eapply store_next;[reflexivity|apply handoff_alias_increment_source with(checked:=checked)|].
        -- rewrite handoff_alias_env_preserved by discriminate;exact CHECKED.
        -- lia.
        -- handoff_route;apply store_done;reflexivity.
      * exact PATH.
Qed.

Theorem handoff_validation_success e le m k handles words index :
  e!EntrySource._handles=Some(handles,tarray tint 4) ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> 0<=index<4 ->
  (forall slot,0<=slot<4 -> Mem.loadv Mint32 m(Vptr handles(Ptrofs.repr(4*slot)))=Some(Vint(words slot))) ->
  4<=Int.signed(words index) ->
  (forall slot,0<=slot<index -> Int.eq(words index)(words slot)=false) ->
  exists count final,
    handoff_descriptor_guard_frame le final /\
    store_path handoff_ge(fun after=>after=m)
      (State EntrySource.f_guest handoff_descriptor_range(Kseq handoff_descriptor_after_range k)e le m)count
      (State EntrySource.f_guest handoff_fd_format(Kseq handoff_descriptor_after_format k)e final m).
Proof.
  intros LOCAL INDEX BOUND LOADS POSITIVE DISTINCT.
  pose proof(handoff_descriptor_range_source e le m(Kseq handoff_descriptor_after_range k)
    handles index(words index)LOCAL INDEX BOUND(LOADS index BOUND))as RANGE.
  rewrite(proj2(Z.ltb_ge(Int.signed(words index))4)POSITIVE)in RANGE.
  set(ranged:=PTree.set EntrySource._t'37(Vint(words index))le).
  set(started:=PTree.set EntrySource._j(Vint Int.zero)ranged).
  destruct(handoff_alias_success e m handles words index(Z.to_nat index)0 started
    (Kseq handoff_descriptor_after_alias k)LOCAL ltac:(lia)ltac:(rewrite Z2Nat.id by lia;lia)ltac:(lia)
    ltac:(unfold started,ranged;rewrite !PTree.gso by discriminate;exact INDEX)
    ltac:(unfold started;apply PTree.gss)LOADS DISTINCT)as[count[final[FRAME ALIASES]]].
  exists(11+count)%nat,final;split.
  - intros id RANGEID J LEFT RIGHT;rewrite FRAME by assumption;unfold started,ranged;rewrite !PTree.gso by congruence;reflexivity.
  - eapply store_path_trans with(n:=4%nat);[exact RANGE|].
    handoff_route;rewrite handoff_descriptor_after_range_actual at 1;handoff_route.
    rewrite handoff_descriptor_aliases_actual at 1;handoff_route;handoff_set.
    + apply old_expression_value,value_int.
    + handoff_route;replace(S(S count))with(count+2)%nat by lia.
      eapply store_path_trans with(n:=count);[exact ALIASES|].
      handoff_route;rewrite handoff_descriptor_after_alias_actual at 1;handoff_route;apply store_done;reflexivity.
Qed.

Theorem handoff_fd_success cell input b words before le k failure index bytes :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  0<=index<4 -> 4<=Int.signed(words index) ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> le!EntrySource._failure=Some(Vint failure) ->
  (1<=length bytes<32)%nat -> Forall(fun byte=>byte<>Byte.zero)bytes ->
  decimal_number bytes=Some(Int.signed(words index)) ->
  exists after final events,
    handoff_live_data cell input b words after /\
    final!EntrySource._i=Some(Vint(Int.repr index)) /\ final!EntrySource._failure=Some(Vint failure) /\
    number_input after(handoff_numbers b)(Ptrofs.repr(32*index))bytes /\
    handoff_encoding_frame cell b(handoff_numbers b)(Ptrofs.repr(32*index))before after /\
    entry_handoff_steps handoff_ge cell
      (live(State EntrySource.f_guest handoff_fd_format(Kseq handoff_descriptor_after_format k)(handoff_locals_env b)le before))events
      (live(State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)).
Proof.
  intros LAYOUT LIVE INDEXBOUND POSITIVE INDEX FAILURE LENGTH NONZERO PARSED.
  set(wanted:=Int.signed(words index)).
  set(returned:=Int.repr(Z.of_nat(length bytes))).
  assert(GOOD:0<Int.signed returned<32).
  { unfold returned;rewrite Int.signed_repr;[lia|change Int.min_signed with(-2147483648);change Int.max_signed with 2147483647;lia]. }
  destruct(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE))as[error ERRNO].
  destruct(handoff_format_bytes_witness cell before(handoff_numbers b)(Ptrofs.repr(32*index))error bytes
    (handoff_numbers_owned _ _ _ (handoff_live_owned _ _ _ _ _ LIVE)INDEXBOUND)ERRNO
    (proj1(handoff_private_object cell input b(handoff_numbers b)128 LAYOUT ltac:(unfold handoff_objects;cbn;auto 8)))
    ltac:(lia)NONZERO)as[formatted[STORE[TEXT[ERRNOAFTER RESULT]]]].
  assert(FORMATTED:handoff_live_data cell input b words formatted)
    by(eapply handoff_live_formatted;[exact LAYOUT|exact LIVE|right;reflexivity|exact RESULT]).
  set(formatle:=handoff_format_env EntrySource._t'34 EntrySource._t'9(Vint(Int.repr wanted))le returned).
  set(checked:=PTree.set EntrySource._t'12(Vint Int.zero)formatle).
  assert(CHECKINDEX:checked!EntrySource._i=Some(Vint(Int.repr index))).
  { unfold checked,formatle,handoff_format_env;rewrite !PTree.gso by discriminate;exact INDEX. }
  assert(WANTED:4<=wanted<=Int.max_signed)by(unfold wanted;pose proof(Int.signed_range(words index));lia).
  assert(HANDLELOAD:Mem.loadv Mint32 formatted(Vptr(handoff_handles b)(Ptrofs.repr(4*index)))=Some(Vint(Int.repr wanted))).
  { unfold wanted;rewrite Int.repr_signed;exact(handoff_live_handles _ _ _ _ _ FORMATTED _ INDEXBOUND). }
  destruct(handoff_uid_numbers_separate b(proj1 LAYOUT))as[UIDNUM[UIDENC NUMENC]].
  assert(HANDLEENC:handoff_handles b<>handoff_encoded b)
    by(apply handoff_local_handles_other;[exact(proj1 LAYOUT)|tauto]).
  destruct(handoff_fd_numeric_source(handoff_locals_env b)checked formatted(Kseq handoff_fd_flags k)
    (handoff_numbers b)(handoff_encoded b)(handoff_handles b)index bytes wanted
    ltac:(unfold handoff_locals_env;WriteAll.lookup)ltac:(unfold handoff_locals_env;WriteAll.lookup)
    ltac:(unfold handoff_locals_env;WriteAll.lookup)ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
    HANDLEENC NUMENC CHECKINDEX INDEXBOUND HANDLELOAD WANTED TEXT
    (handoff_encoded_owned _ _ (handoff_live_owned _ _ _ _ _ FORMATTED)))
    as[count[after[BOUND[POST[AFTERTEXT NUMBERPATH]]]]].
  assert(AFTER:handoff_live_data cell input b words after)
    by(eapply handoff_live_number;[exact LAYOUT|exact FORMATTED|exact POST]).
  assert(BAD:handoff_numeric_bad(decimal_number bytes)wanted=false)by(apply handoff_numeric_good;exact PARSED).
  rewrite BAD in NUMBERPATH.
  set(numberle:=handoff_numeric_env EntrySource._t'13 EntrySource._t'14 EntrySource._t'32 EntrySource._t'33
    checked(decimal_number bytes)wanted(Vint(Int.repr wanted))).
  assert(NUMBERINDEX:numberle!EntrySource._i=Some(Vint(Int.repr index))).
  { unfold numberle,handoff_numeric_env;rewrite PARSED;repeat rewrite PTree.gso by discriminate;exact CHECKINDEX. }
  set(final:=PTree.set EntrySource._t'16(Vint Int.zero)(PTree.set EntrySource._t'31(Vint(words index))numberle)).
  exists after,final;eexists;split;[exact AFTER|]. split.
  - unfold final;rewrite !PTree.gso by discriminate;exact NUMBERINDEX.
  - split.
    + unfold final,numberle,handoff_numeric_env;rewrite PARSED;unfold checked,formatle,handoff_format_env;
        repeat rewrite PTree.gso by discriminate;exact FAILURE.
    + split;[exact AFTERTEXT|]. split.
      * eapply handoff_encoding_frame_trans;[eapply handoff_encoding_formatted;exact RESULT|eapply handoff_encoding_number;exact POST].
      * eapply handoff_success_path.
        -- apply handoff_fd_format_call_source with(handles:=handoff_handles b)(index:=index)(wanted:=wanted).
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ unfold handoff_locals_env;WriteAll.lookup.
           ++ unfold handoff_locals_env;WriteAll.lookup.
           ++ exact INDEX.
           ++ exact INDEXBOUND.
           ++ unfold wanted;rewrite Int.repr_signed;exact(handoff_live_handles _ _ _ _ _ LIVE _ INDEXBOUND).
           ++ exact WANTED.
        -- econstructor.
           ++ apply entry_format_step;[apply handoff_numbers_owned;[exact(handoff_live_owned _ _ _ _ _ LIVE)|exact INDEXBOUND]|exact RESULT].
           ++ eapply handoff_success_path;[apply handoff_format_return_source;discriminate|].
              handoff_success_route;rewrite handoff_fd_after_format_actual at 1;handoff_success_route.
              rewrite handoff_fd_count_actual at 1;eapply handoff_success_path.
              ** apply handoff_count_success_source with(count:=returned).
                 --- unfold formatle,handoff_format_env;apply PTree.gss.
                 --- exact GOOD.
              ** handoff_success_route;rewrite handoff_fd_after_count_actual at 1;handoff_success_route.
                 eapply handoff_success_path;[exact NUMBERPATH|]. handoff_success_route.
                 eapply handoff_success_path.
                 --- apply handoff_fd_flags_call_source with(handles:=handoff_handles b)(index:=index).
                     +++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
                     +++ unfold handoff_locals_env;WriteAll.lookup.
                     +++ exact NUMBERINDEX.
                     +++ exact INDEXBOUND.
                     +++ exact(handoff_live_handles _ _ _ _ _ AFTER _ INDEXBOUND).
                 --- econstructor.
                     +++ apply entry_flags_step with(returned:=Int.zero);[apply Mem.unchanged_on_refl|exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ AFTER))].
                     +++ unfold handoff_flags_fd_cont;eapply handoff_success_path;[apply handoff_flags_return_source|constructor].
Qed.
