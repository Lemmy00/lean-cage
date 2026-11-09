(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The real four-slot loop accumulates checked descriptor values and owned numeric bytes. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine HandoffRegion NativeHandoffStructure
  NativeHandoffArguments NativeHandoffAllocation NativeHandoffInput NativeHandoffNumeric NativeHandoffMemory
  NativeHandoffFormat NativeHandoffDescriptors NativeHandoffFlags NativeHandoffEncoding.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberInitial.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Fixpoint handoff_fd_history b words m start (texts:list(list Byte.int)) : Prop :=
  match texts with
  | []=>True
  | bytes::rest=>number_input m (handoff_numbers b)(Ptrofs.repr(32*start)) bytes /\
      (1<=length bytes<32)%nat /\ decimal_number bytes=Some(Int.signed(words start)) /\
      handoff_fd_history b words m (start+1) rest
  end.
Definition handoff_descriptors_checked words index := forall slot,0<=slot<index ->
  4<=Int.signed(words slot) /\ forall previous,0<=previous<slot -> Int.eq(words slot)(words previous)=false.

Lemma handoff_fd_history_snoc b words m : forall texts start bytes,
  handoff_fd_history b words m start texts ->
  number_input m (handoff_numbers b)(Ptrofs.repr(32*(start+Z.of_nat(length texts)))) bytes ->
  (1<=length bytes<32)%nat ->
  decimal_number bytes=Some (Int.signed (words (start + Z.of_nat (length texts)))) ->
  handoff_fd_history b words m start (texts++[bytes]).
Proof.
  induction texts as[|head rest IH];intros start bytes HISTORY TEXT LENGTH PARSED.
  - cbn [handoff_fd_history length] in *;rewrite Z.add_0_r in TEXT,PARSED.
    split;[exact TEXT|]. split;[exact LENGTH|]. split;[exact PARSED|exact I].
  - cbn [handoff_fd_history] in HISTORY |- *;destruct HISTORY as[HEAD[HEADLEN[HEADPARSED REST]]].
    split;[exact HEAD|]. split;[exact HEADLEN|]. split;[exact HEADPARSED|].
    apply IH;[exact REST| |exact LENGTH|].
    + replace(start+1+Z.of_nat(length rest))with(start+Z.of_nat(length(head::rest)))by
        (cbn [length];rewrite Nat2Z.inj_succ;lia);exact TEXT.
    + replace(start+1+Z.of_nat(length rest))with(start+Z.of_nat(length(head::rest)))by
        (cbn [length];rewrite Nat2Z.inj_succ;lia);exact PARSED.
Qed.

Lemma handoff_fd_history_preserved cell input b words before after index : forall texts start,
  handoff_private_layout cell input b ->
  handoff_encoding_frame cell b(handoff_numbers b)(Ptrofs.repr(32*index)) before after ->
  0<=start -> start+Z.of_nat(length texts)<=index -> index<4 ->
  handoff_fd_history b words before start texts -> handoff_fd_history b words after start texts.
Proof.
  induction texts as[|bytes rest IH];intros start LAYOUT FRAME LOW HIGH INDEX HISTORY;[exact I|].
  cbn [handoff_fd_history] in HISTORY |- *;destruct HISTORY as[TEXT[LENGTH[PARSED REST]]].
  split.
  - eapply handoff_encoding_preserves_previous;[exact LAYOUT| |exact INDEX|lia|exact FRAME|exact TEXT].
    cbn [length] in HIGH;rewrite Nat2Z.inj_succ in HIGH;lia.
  - split;[exact LENGTH|]. split;[exact PARSED|].
    apply IH;try assumption;[lia|]. cbn [length] in HIGH;rewrite Nat2Z.inj_succ in HIGH;lia.
Qed.

Lemma handoff_descriptors_checked_extend words index :
  handoff_descriptors_checked words index -> 4<=Int.signed(words index) ->
  (forall previous,0<=previous<index->Int.eq(words index)(words previous)=false) ->
  handoff_descriptors_checked words(index+1).
Proof.
  intros CHECKED POSITIVE DISTINCT slot BOUND.
  destruct(Z.eq_dec slot index) as[SAME|OTHER];[subst;auto|apply CHECKED;lia].
Qed.

Theorem handoff_descriptors_iterations_region cell input b words failure R budget :
  forall slots index texts before le k uidbytes,
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  0<=index -> index+Z.of_nat slots=4 -> length texts=Z.to_nat index ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> le!EntrySource._failure=Some(Vint failure) ->
  number_input before(handoff_uid b)Ptrofs.zero uidbytes ->
  handoff_fd_history b words before 0 texts -> handoff_descriptors_checked words index ->
  (forall state,handoff_failure_result cell failure state->R state) ->
  (forall after final completed,
    handoff_live_data cell input b words after ->
    final!EntrySource._failure=Some(Vint failure) ->
    number_input after(handoff_uid b)Ptrofs.zero uidbytes ->
    handoff_fd_history b words after 0 completed -> length completed=4%nat ->
    handoff_descriptors_checked words 4 ->
    handoff_region handoff_ge cell(fun _=>True) R budget
      (State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)) ->
  handoff_region handoff_ge cell(fun _=>True) R (slots*5000+5+budget)
    (State EntrySource.f_guest handoff_descriptor_iterations k(handoff_locals_env b)le before).
Proof.
  induction slots as[|slots IH];intros index texts before le k uidbytes LAYOUT LIVE LOW END LENGTH INDEX FAILURE
    UIDTEXT HISTORY CHECKED ACCEPT NEXT.
  - cbn [Z.of_nat] in END;assert(index=4)by lia;subst index.
    eapply handoff_region_store_path with(count:=5%nat)(remaining:=budget).
    + eapply number_path_implication with(P:=fun after=>after=before);[intros;exact I|].
      apply handoff_descriptor_exit_source;exact INDEX.
    + apply NEXT with(completed:=texts);try assumption;exact LENGTH.
  - assert(INDEXBOUND:0<=index<4)by(rewrite Nat2Z.inj_succ in END;lia).
    set(loopk:=Kloop1 handoff_descriptor_body handoff_descriptor_increment k).
    destruct(handoff_descriptor_validation_source(handoff_locals_env b)le before loopk(handoff_handles b)words index
      ltac:(unfold handoff_locals_env;WriteAll.lookup) INDEX INDEXBOUND
      (handoff_live_handles _ _ _ _ _ LIVE))
      as[count[endpoint[validated[BOUND[FRAME[PATH OUTCOME]]]]]].
    assert(VALIDINDEX:validated!EntrySource._i=Some(Vint(Int.repr index))).
    { rewrite FRAME by discriminate;exact INDEX. }
    assert(VALIDFAILURE:validated!EntrySource._failure=Some(Vint failure)).
    { rewrite FRAME by discriminate;exact FAILURE. }
    eapply handoff_region_weaken with(n:=(5+count+(4500+3+(slots*5000+5+budget)))%nat);[|lia].
    eapply handoff_region_store_path with(count:=5%nat).
    + eapply number_path_implication with(P:=fun after=>after=before);[intros;exact I|].
      apply handoff_descriptor_iteration_source with(index:=index);assumption.
    + eapply handoff_region_store_path with(count:=count).
      * eapply number_path_implication with(P:=fun after=>after=before);[intros;exact I|exact PATH].
      * destruct OUTCOME as[[ENDPOINT[POSITIVE DISTINCT]]|[failure_k ENDPOINT]];subst endpoint.
        -- replace(4500+3+(slots*5000+5+budget))%nat with(4500+(3+(slots*5000+5+budget)))%nat by lia.
           refine(handoff_fd_encoding_region cell input b words before validated loopk failure index R
             (3+(slots*5000+5+budget))%nat LAYOUT LIVE INDEXBOUND POSITIVE VALIDINDEX VALIDFAILURE ACCEPT _).
           intros after final bytes AFTER INDEXFINAL FAILUREFINAL TEXT BYTES PARSED ENCODEDFRAME.
           assert(AFTERUID:number_input after(handoff_uid b)Ptrofs.zero uidbytes)
             by(eapply handoff_encoding_preserves_uid;[exact LAYOUT|exact ENCODEDFRAME|exact UIDTEXT]).
           assert(AFTERHISTORY:handoff_fd_history b words after 0 texts).
           { eapply handoff_fd_history_preserved;[exact LAYOUT|exact ENCODEDFRAME|lia| |lia|exact HISTORY].
             rewrite LENGTH,Z2Nat.id by lia;lia. }
           assert(COMPLETED:handoff_fd_history b words after 0(texts++[bytes])).
           { apply handoff_fd_history_snoc;[exact AFTERHISTORY| |exact BYTES|].
             - rewrite LENGTH,Z2Nat.id by lia;replace(0+index)with index by lia;exact TEXT.
             - rewrite LENGTH,Z2Nat.id by lia;replace(0+index)with index by lia;exact PARSED. }
           assert(COMPLETEDLENGTH:length(texts++[bytes])=Z.to_nat(index+1)).
           { rewrite length_app;cbn [length];rewrite LENGTH,Z2Nat.inj_add by lia;cbn;lia. }
           assert(COMPLETEDCHECKED:handoff_descriptors_checked words(index+1))
             by(apply handoff_descriptors_checked_extend;assumption).
           eapply handoff_region_store_path with(count:=3%nat)(remaining:=(slots*5000+5+budget)%nat).
           ++ eapply number_path_implication with(P:=fun current=>current=after);[intros;exact I|].
              apply handoff_descriptor_increment_source with(index:=index);assumption.
           ++ apply IH with(index:=index+1)(texts:=texts++[bytes])(uidbytes:=uidbytes);try assumption.
              ** lia.
              ** rewrite Nat2Z.inj_succ in END;lia.
              ** apply PTree.gss.
              ** rewrite PTree.gso by discriminate;exact FAILUREFINAL.
        -- eapply handoff_region_weaken with(n:=1%nat);[|lia].
           apply handoff_const_failure_region with(failure:=failure)(remaining:=0%nat).
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ exact VALIDFAILURE.
           ++ right;reflexivity.
           ++ change(1<=9<=4095);lia.
           ++ exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE)).
           ++ exact ACCEPT.
Qed.

Theorem handoff_descriptors_region cell input b words before le k failure uidbytes R budget :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  le!EntrySource._failure=Some(Vint failure) ->
  number_input before(handoff_uid b)Ptrofs.zero uidbytes ->
  (forall state,handoff_failure_result cell failure state->R state) ->
  (forall after final texts,
    handoff_live_data cell input b words after -> final!EntrySource._failure=Some(Vint failure) ->
    number_input after(handoff_uid b)Ptrofs.zero uidbytes ->
    handoff_fd_history b words after 0 texts -> length texts=4%nat ->
    handoff_descriptors_checked words 4 ->
    handoff_region handoff_ge cell(fun _=>True) R budget
      (State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)) ->
  handoff_region handoff_ge cell(fun _=>True) R (20008+budget)
    (State EntrySource.f_guest handoff_descriptor_loop k(handoff_locals_env b)le before).
Proof.
  intros LAYOUT LIVE FAILURE UIDTEXT ACCEPT NEXT;rewrite handoff_descriptor_loop_actual at 1.
  eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
  eapply handoff_region_source_prepend;[exact I|apply certified_set_edge|].
  - apply old_expression_value,value_int.
  - eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
    apply handoff_descriptors_iterations_region with(input:=input)(words:=words)(slots:=4%nat)(index:=0)(texts:=[])(failure:=failure)(uidbytes:=uidbytes);
      try assumption;try lia;try reflexivity.
    + apply PTree.gss.
    + rewrite PTree.gso by discriminate;exact FAILURE.
    + intros slot BOUND;lia.
Qed.

Lemma handoff_fd_history_errno cell input b words before after : forall texts start,
  handoff_private_layout cell input b -> entry_errno_frame cell before after ->
  handoff_fd_history b words before start texts -> handoff_fd_history b words after start texts.
Proof.
  induction texts as[|bytes rest IH];intros start LAYOUT FRAME HISTORY;[exact I|].
  cbn[handoff_fd_history]in HISTORY|-*;destruct HISTORY as[TEXT[LENGTH[PARSED REST]]].
  split.
  - eapply handoff_errno_preserves_input;[exact FRAME| |exact TEXT].
    exact(proj1(handoff_private_object cell input b(handoff_numbers b)128 LAYOUT
      ltac:(unfold handoff_objects;cbn;auto 8))).
  - split;[exact LENGTH|]. split;[exact PARSED|]. apply IH;assumption.
Qed.

Lemma handoff_fd_history_tables b words before after : forall texts start,
  NoDup(map fst(handoff_objects b)) -> handoff_tables_frame b before after ->
  handoff_fd_history b words before start texts -> handoff_fd_history b words after start texts.
Proof.
  induction texts as[|bytes rest IH];intros start DISTINCT FRAME HISTORY;[exact I|].
  cbn[handoff_fd_history]in HISTORY|-*;destruct HISTORY as[TEXT[LENGTH[PARSED REST]]].
  destruct(handoff_tables_numbers_separate b DISTINCT)as[UIDARGS[UIDENV[NUMARGS NUMENV]]].
  split.
  - eapply handoff_tables_preserves_input;[exact FRAME|exact NUMARGS|exact NUMENV|exact TEXT].
  - split;[exact LENGTH|]. split;[exact PARSED|]. apply IH;assumption.
Qed.
