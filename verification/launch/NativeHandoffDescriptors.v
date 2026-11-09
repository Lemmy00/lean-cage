(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Validate the actual source descriptor slots before encoding or changing flags. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffStructure NativeHandoffArguments
  NativeHandoffNumeric NativeHandoffFormat.
Import ListNotations.
Open Scope Z_scope.

Definition handoff_descriptor_failure :=
  Scall None (Evar EntrySource._fail_child (Tfunction [tint;tuint;tint] tvoid cc_default))
    [Etempvar EntrySource._failure tint; Econst_int (Int.repr 3) tint; Econst_int (Int.repr 9) tint].

Definition handoff_descriptor_loop := guest_phase 9.
Definition handoff_descriptor_iterations := match handoff_descriptor_loop with
  | Ssequence _ (Sloop body increment) => Sloop body increment | _ => Sskip end.
Definition handoff_descriptor_body := match handoff_descriptor_iterations with
  | Sloop body _ => body | _ => Sskip end.
Definition handoff_descriptor_increment := match handoff_descriptor_iterations with
  | Sloop _ increment => increment | _ => Sskip end.
Definition handoff_descriptor_test := match handoff_descriptor_body with
  | Ssequence test _ => test | _ => Sskip end.
Definition handoff_descriptor_range := match handoff_descriptor_body with
  | Ssequence _ (Ssequence test _) => test | _ => Sskip end.
Definition handoff_descriptor_after_range := match handoff_descriptor_body with
  | Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition handoff_descriptor_aliases := match handoff_descriptor_after_range with
  | Ssequence test _ => test | _ => Sskip end.
Definition handoff_descriptor_alias_loop := match handoff_descriptor_aliases with
  | Ssequence _ loop => loop | _ => Sskip end.
Definition handoff_descriptor_alias_body := match handoff_descriptor_alias_loop with
  | Sloop body _ => body | _ => Sskip end.
Definition handoff_descriptor_alias_increment := match handoff_descriptor_alias_loop with
  | Sloop _ increment => increment | _ => Sskip end.

Definition handoff_descriptor_at index :=
  Ederef (Ebinop Oadd (Evar EntrySource._handles (tarray tint 4))
    (Etempvar index tuint) (tptr tint)) tint.

Lemma handoff_descriptor_range_actual : handoff_descriptor_range =
  Ssequence (Sset EntrySource._t'37 (handoff_descriptor_at EntrySource._i))
    (Sifthenelse (Ebinop Olt (Etempvar EntrySource._t'37 tint) (Econst_int (Int.repr 4) tint) tint)
      handoff_descriptor_failure Sskip).
Proof. reflexivity. Qed.

Lemma handoff_descriptor_alias_actual : handoff_descriptor_alias_loop =
  Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar EntrySource._j tuint) (Etempvar EntrySource._i tuint) tint) Sskip Sbreak)
      (Ssequence
        (Sset EntrySource._t'35 (handoff_descriptor_at EntrySource._i))
        (Ssequence
          (Sset EntrySource._t'36 (handoff_descriptor_at EntrySource._j))
          (Sifthenelse (Ebinop Oeq (Etempvar EntrySource._t'35 tint) (Etempvar EntrySource._t'36 tint) tint)
            handoff_descriptor_failure Sskip))))
    (Sset EntrySource._j (Ebinop Oadd (Etempvar EntrySource._j tuint) (Econst_int Int.one tint) tuint)).
Proof. reflexivity. Qed.

Lemma handoff_descriptor_at_value e le m handles index slot word :
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  le ! slot = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * index))) = Some (Vint word) ->
  expression_value handoff_ge e le m (handoff_descriptor_at slot) (Vint word).
Proof.
  intros LOCAL INDEX BOUND LOAD; unfold handoff_descriptor_at.
  eapply location_read_value.
  - apply pointer_location_value; eapply binary_expression_value.
    + apply handoff_array_value; exact LOCAL.
    + apply old_expression_value; apply value_temp; exact INDEX.
    + apply handoff_native_array_index_unsigned with (stride := 4) (index := index); [reflexivity|lia|lia].
  - eapply deref_loc_value; [reflexivity|exact LOAD].
Qed.

Lemma handoff_descriptor_lower ge m word :
  sem_binary_operation ge Olt (Vint word) tint (Vint (Int.repr 4)) tint m =
    Some (Val.of_bool (Int.signed word <? 4)).
Proof.
  change (Some (Val.of_bool (Int.lt word (Int.repr 4))) = Some (Val.of_bool (Int.signed word <? 4))).
  unfold Int.lt; change (Some (Val.of_bool (if zlt (Int.signed word) 4 then true else false)) =
    Some (Val.of_bool (Int.signed word <? 4))).
  destruct (zlt (Int.signed word) 4) as [LOW|HIGH].
  - rewrite (proj2 (Z.ltb_lt (Int.signed word) 4) LOW); reflexivity.
  - rewrite (proj2 (Z.ltb_ge (Int.signed word) 4) ltac:(lia)); reflexivity.
Qed.

Theorem handoff_descriptor_range_source e le m k handles index word :
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * index))) = Some (Vint word) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest handoff_descriptor_range k e le m) 4
    (State EntrySource.f_guest
      (if Int.signed word <? 4 then handoff_descriptor_failure else Sskip) k e
      (PTree.set EntrySource._t'37 (Vint word) le) m).
Proof.
  intros LOCAL INDEX BOUND LOAD; rewrite handoff_descriptor_range_actual.
  handoff_route; handoff_set.
  - apply handoff_descriptor_at_value with (handles := handles) (index := index); [exact LOCAL|exact INDEX|exact BOUND|exact LOAD].
  - handoff_route.
    eapply store_next; [reflexivity|apply certified_if_edge with
      (v := Val.of_bool (Int.signed word <? 4)) (b := Int.signed word <? 4)|].
    + eapply binary_expression_value.
      * apply old_expression_value; apply value_temp; apply PTree.gss.
      * apply old_expression_value; apply value_int.
      * apply handoff_descriptor_lower.
    + apply NumberControl.number_bool_value.
    + apply store_done; reflexivity.
Qed.

Definition handoff_alias_env le left right :=
  PTree.set EntrySource._t'36 (Vint right) (PTree.set EntrySource._t'35 (Vint left) le).

Definition handoff_alias_compare :=
  Ssequence (Sset EntrySource._t'35 (handoff_descriptor_at EntrySource._i))
    (Ssequence (Sset EntrySource._t'36 (handoff_descriptor_at EntrySource._j))
      (Sifthenelse (Ebinop Oeq (Etempvar EntrySource._t'35 tint) (Etempvar EntrySource._t'36 tint) tint)
        handoff_descriptor_failure Sskip)).

Definition handoff_alias_test :=
  Sifthenelse (Ebinop Olt (Etempvar EntrySource._j tuint) (Etempvar EntrySource._i tuint) tint)
    Sskip Sbreak.

Lemma handoff_alias_body_actual : handoff_descriptor_alias_body =
  Ssequence handoff_alias_test handoff_alias_compare.
Proof. reflexivity. Qed.
Lemma handoff_alias_loop_actual : handoff_descriptor_alias_loop =
  Sloop handoff_descriptor_alias_body handoff_descriptor_alias_increment.
Proof. reflexivity. Qed.

Lemma handoff_alias_test_operation ge m index checked : 0 <= checked <= index /\ index <= 4 ->
  sem_binary_operation ge Olt (Vint (Int.repr checked)) tuint (Vint (Int.repr index)) tuint m =
    Some (Val.of_bool (checked <? index)).
Proof.
  intros BOUNDS.
  change (Some (Val.of_bool (Int.ltu (Int.repr checked) (Int.repr index))) =
    Some (Val.of_bool (checked <? index))).
  unfold Int.ltu; rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  destruct (zlt checked index) as [LOW|HIGH].
  - rewrite (proj2 (Z.ltb_lt checked index) LOW); reflexivity.
  - rewrite (proj2 (Z.ltb_ge checked index) ltac:(lia)); reflexivity.
Qed.

Lemma handoff_alias_compare_source e le m k handles index checked left right :
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) ->
  le ! EntrySource._j = Some (Vint (Int.repr checked)) ->
  0 <= index < 4 -> 0 <= checked < 4 ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * index))) = Some (Vint left) ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * checked))) = Some (Vint right) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest handoff_alias_compare k e le m) 7
    (State EntrySource.f_guest (if Int.eq left right then handoff_descriptor_failure else Sskip)
      k e (handoff_alias_env le left right) m).
Proof.
  intros LOCAL INDEX CHECKED INDEXBOUND CHECKEDBOUND LEFT RIGHT.
  unfold handoff_alias_compare, handoff_alias_env.
  handoff_route; handoff_set.
  - eapply handoff_descriptor_at_value; [exact LOCAL|exact INDEX|exact INDEXBOUND|exact LEFT].
  - handoff_route; handoff_route; handoff_set.
    + eapply handoff_descriptor_at_value; [exact LOCAL| |exact CHECKEDBOUND|exact RIGHT].
      rewrite PTree.gso by discriminate; exact CHECKED.
    + handoff_route.
      eapply store_next; [reflexivity|apply certified_if_edge with
        (v := Val.of_bool (Int.eq left right)) (b := Int.eq left right)|].
      * eapply binary_expression_value.
        -- apply old_expression_value; apply value_temp.
           rewrite PTree.gso by discriminate; apply PTree.gss.
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- reflexivity.
      * apply NumberControl.number_bool_value.
      * apply store_done; reflexivity.
Qed.

Lemma handoff_alias_env_preserved le left right id :
  id <> EntrySource._t'35 -> id <> EntrySource._t'36 ->
  (handoff_alias_env le left right) ! id = le ! id.
Proof. intros LEFT RIGHT; unfold handoff_alias_env; rewrite !PTree.gso by congruence; reflexivity. Qed.

Lemma handoff_alias_increment_source e le m k checked :
  le ! EntrySource._j = Some (Vint (Int.repr checked)) -> 0 <= checked <= 4 ->
  store_edge handoff_ge
    (State EntrySource.f_guest handoff_descriptor_alias_increment k e le m)
    (State EntrySource.f_guest Sskip k e (PTree.set EntrySource._j (Vint (Int.repr (checked+1))) le) m).
Proof.
  intros INDEX BOUND; apply certified_set_edge.
  eapply binary_expression_value.
  - apply old_expression_value; apply value_temp; exact INDEX.
  - apply old_expression_value; apply value_int.
  - change (Some (Vint (Int.add (Int.repr checked) Int.one)) = Some (Vint (Int.repr (checked+1)))).
    unfold Int.add; change (Some (Vint (Int.repr (Int.unsigned (Int.repr checked)+1))) =
      Some (Vint (Int.repr (checked+1)))).
    rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia); reflexivity.
Qed.

Lemma handoff_alias_test_edge e le m k index checked :
  le ! EntrySource._i = Some (Vint (Int.repr index)) ->
  le ! EntrySource._j = Some (Vint (Int.repr checked)) ->
  0 <= checked <= index /\ index <= 4 ->
  store_edge handoff_ge (State EntrySource.f_guest handoff_alias_test k e le m)
    (State EntrySource.f_guest (if checked <? index then Sskip else Sbreak) k e le m).
Proof.
  intros INDEX CHECKED BOUNDS; apply certified_if_edge with (v := Val.of_bool (checked <? index)).
  - eapply binary_expression_value.
    + apply old_expression_value; apply value_temp; exact CHECKED.
    + apply old_expression_value; apply value_temp; exact INDEX.
    + apply handoff_alias_test_operation; exact BOUNDS.
  - apply NumberControl.number_bool_value.
Qed.

Lemma handoff_alias_iteration_source e le m k handles index checked left right :
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) ->
  le ! EntrySource._j = Some (Vint (Int.repr checked)) ->
  0 <= checked < index -> index < 4 ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * index))) = Some (Vint left) ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * checked))) = Some (Vint right) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest handoff_descriptor_alias_loop k e le m) 11
    (State EntrySource.f_guest (if Int.eq left right then handoff_descriptor_failure else Sskip)
      (Kloop1 handoff_descriptor_alias_body handoff_descriptor_alias_increment k)
      e (handoff_alias_env le left right) m).
Proof.
  intros LOCAL INDEX CHECKED ORDER BOUND LEFT RIGHT.
  eapply store_path_trans with (n := 4%nat).
  - rewrite handoff_alias_loop_actual at 1; handoff_route.
    rewrite handoff_alias_body_actual at 1; handoff_route.
    eapply store_next; [reflexivity|apply handoff_alias_test_edge with (index:=index) (checked:=checked); [exact INDEX|exact CHECKED|lia]|].
    rewrite (proj2 (Z.ltb_lt checked index) ltac:(lia)); handoff_route; apply store_done; reflexivity.
  - apply handoff_alias_compare_source with (handles:=handles) (index:=index) (checked:=checked); assumption || lia.
Qed.

Definition handoff_alias_temp_frame (le final : temp_env) := forall id,
  id <> EntrySource._j -> id <> EntrySource._t'35 -> id <> EntrySource._t'36 ->
  final ! id = le ! id.

Theorem handoff_alias_loop_source e m handles words index : forall remaining checked le k,
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  0 <= checked -> checked + Z.of_nat remaining = index -> index < 4 ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) ->
  le ! EntrySource._j = Some (Vint (Int.repr checked)) ->
  (forall slot, 0 <= slot < 4 ->
    Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * slot))) = Some (Vint (words slot))) ->
  exists count terminal final,
    (count <= 14 * remaining + 5)%nat /\
    handoff_alias_temp_frame le final /\
    store_path handoff_ge (fun after => after = m)
      (State EntrySource.f_guest handoff_descriptor_alias_loop k e le m) count terminal /\
    ((terminal = State EntrySource.f_guest Sskip k e final m /\
      forall slot, checked <= slot < index -> Int.eq (words index) (words slot) = false) \/
      exists failure_k, terminal = State EntrySource.f_guest handoff_descriptor_failure failure_k e final m).
Proof.
  induction remaining as [|remaining IH]; intros checked le k LOCAL LOW END HIGH INDEX CHECKED LOADS.
  - cbn [Z.of_nat] in END; assert (checked=index) by lia; subst checked.
    exists 5%nat,(State EntrySource.f_guest Sskip k e le m),le.
    split; [lia|]. split; [intros id J LEFT RIGHT; reflexivity|]. split.
    + rewrite handoff_alias_loop_actual at 1; handoff_route.
      rewrite handoff_alias_body_actual at 1; handoff_route.
      eapply store_next; [reflexivity|apply handoff_alias_test_edge with (index:=index) (checked:=index); [exact INDEX|exact CHECKED|lia]|].
      rewrite Z.ltb_irrefl; handoff_route; handoff_route; apply store_done; reflexivity.
    + left; split; [reflexivity|intros; lia].
  - assert (ORDER : 0 <= checked < index) by (rewrite Nat2Z.inj_succ in END; lia).
    pose proof (handoff_alias_iteration_source e le m k handles index checked (words index) (words checked)
      LOCAL INDEX CHECKED ORDER HIGH (LOADS index ltac:(lia)) (LOADS checked ltac:(lia))) as ITERATION.
    destruct (Int.eq (words index) (words checked)) eqn:EQUAL.
    + exists 11%nat,
        (State EntrySource.f_guest handoff_descriptor_failure
          (Kloop1 handoff_descriptor_alias_body handoff_descriptor_alias_increment k)
          e (handoff_alias_env le (words index) (words checked)) m),
        (handoff_alias_env le (words index) (words checked)).
      split; [lia|]. split.
      * intros id J LEFT RIGHT; apply handoff_alias_env_preserved; assumption.
      * split; [exact ITERATION|right; eexists; reflexivity].
    + set (next := PTree.set EntrySource._j (Vint (Int.repr (checked+1)))
        (handoff_alias_env le (words index) (words checked))).
      assert (NEXTINDEX : next ! EntrySource._i = Some (Vint (Int.repr index))).
      { unfold next; rewrite PTree.gso by discriminate.
        rewrite handoff_alias_env_preserved by discriminate; exact INDEX. }
      destruct (IH (checked+1) next k LOCAL ltac:(lia)
        ltac:(rewrite Nat2Z.inj_succ in END; lia) HIGH NEXTINDEX
        ltac:(unfold next; apply PTree.gss) LOADS)
        as [count [terminal [final [BOUND [FRAME [PATH OUTCOME]]]]]].
      exists (14+count)%nat,terminal,final; split; [lia|]. split.
      * intros id J LEFT RIGHT; rewrite FRAME by assumption.
        unfold next; rewrite PTree.gso by congruence; apply handoff_alias_env_preserved; assumption.
      * split.
        -- eapply store_path_trans with (n:=11%nat); [exact ITERATION|].
           eapply store_path_trans with (n:=3%nat) (b:=
             State EntrySource.f_guest handoff_descriptor_alias_loop k e next m).
           ++ handoff_route.
              eapply store_next; [reflexivity|apply handoff_alias_increment_source with (checked:=checked)|].
              ** rewrite handoff_alias_env_preserved by discriminate; exact CHECKED.
              ** lia.
              ** handoff_route; apply store_done; reflexivity.
           ++ exact PATH.
        -- destruct OUTCOME as [[TERMINAL DISTINCT]|FAILURE]; [left|right; exact FAILURE].
           split; [exact TERMINAL|]. intros slot SLOT.
           destruct (Z.eq_dec slot checked) as [SAME|DIFFERENT].
           ++ subst slot; exact EQUAL.
           ++ apply DISTINCT; lia.
Qed.

Definition handoff_descriptor_after_alias := match handoff_descriptor_after_range with
  | Ssequence _ rest => rest | _ => Sskip end.
Definition handoff_descriptor_after_format := match handoff_descriptor_after_alias with
  | Ssequence _ rest => rest | _ => Sskip end.

Lemma handoff_descriptor_body_actual : handoff_descriptor_body =
  Ssequence handoff_descriptor_test
    (Ssequence handoff_descriptor_range handoff_descriptor_after_range).
Proof. reflexivity. Qed.
Lemma handoff_descriptor_after_range_actual : handoff_descriptor_after_range =
  Ssequence handoff_descriptor_aliases handoff_descriptor_after_alias.
Proof. reflexivity. Qed.
Lemma handoff_descriptor_aliases_actual : handoff_descriptor_aliases =
  Ssequence (Sset EntrySource._j (Econst_int Int.zero tint)) handoff_descriptor_alias_loop.
Proof. reflexivity. Qed.
Lemma handoff_descriptor_after_alias_actual : handoff_descriptor_after_alias =
  Ssequence handoff_fd_format handoff_descriptor_after_format.
Proof. reflexivity. Qed.

Definition handoff_descriptor_guard_frame (le final : temp_env) := forall id,
  id <> EntrySource._t'37 -> id <> EntrySource._j ->
  id <> EntrySource._t'35 -> id <> EntrySource._t'36 -> final ! id = le ! id.

Theorem handoff_descriptor_validation_source e le m k handles words index :
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  (forall slot, 0 <= slot < 4 ->
    Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * slot))) = Some (Vint (words slot))) ->
  exists count terminal final,
    (count <= 58)%nat /\ handoff_descriptor_guard_frame le final /\
    store_path handoff_ge (fun after => after=m)
      (State EntrySource.f_guest handoff_descriptor_range
        (Kseq handoff_descriptor_after_range k) e le m) count terminal /\
    ((terminal = State EntrySource.f_guest handoff_fd_format
        (Kseq handoff_descriptor_after_format k) e final m /\
      4 <= Int.signed (words index) /\
      forall slot, 0 <= slot < index -> Int.eq (words index) (words slot) = false) \/
      exists failure_k, terminal = State EntrySource.f_guest handoff_descriptor_failure failure_k e final m).
Proof.
  intros LOCAL INDEX BOUND LOADS.
  pose proof (handoff_descriptor_range_source e le m (Kseq handoff_descriptor_after_range k)
    handles index (words index) LOCAL INDEX BOUND (LOADS index BOUND)) as RANGE.
  set (ranged := PTree.set EntrySource._t'37 (Vint (words index)) le).
  destruct (Int.signed (words index) <? 4) eqn:LOWER.
  - exists 4%nat,
      (State EntrySource.f_guest handoff_descriptor_failure (Kseq handoff_descriptor_after_range k) e ranged m),ranged.
    split; [lia|]. split.
    + intros id RANGEID J LEFT RIGHT; unfold ranged; rewrite PTree.gso by congruence; reflexivity.
    + split; [exact RANGE|right; eexists; reflexivity].
  - apply Z.ltb_ge in LOWER.
    set (started := PTree.set EntrySource._j (Vint Int.zero) ranged).
    destruct (handoff_alias_loop_source e m handles words index (Z.to_nat index) 0 started
      (Kseq handoff_descriptor_after_alias k) LOCAL ltac:(lia)
      ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
      ltac:(unfold started,ranged; rewrite !PTree.gso by discriminate; exact INDEX)
      ltac:(unfold started; apply PTree.gss) LOADS)
      as [aliascount [endpoint [final [ALIASBOUND [FRAME [ALIASES OUTCOME]]]]]].
    assert (GUARDFRAME : handoff_descriptor_guard_frame le final).
    { intros id RANGEID J LEFT RIGHT; rewrite FRAME by assumption.
      unfold started,ranged; rewrite !PTree.gso by congruence; reflexivity. }
    assert (START : store_path handoff_ge (fun after=>after=m)
      (State EntrySource.f_guest handoff_descriptor_range (Kseq handoff_descriptor_after_range k) e le m) 9
      (State EntrySource.f_guest handoff_descriptor_alias_loop
        (Kseq handoff_descriptor_after_alias k) e started m)).
    { eapply store_path_trans with (n:=4%nat); [exact RANGE|].
      handoff_route; rewrite handoff_descriptor_after_range_actual at 1; handoff_route.
      rewrite handoff_descriptor_aliases_actual at 1; handoff_route; handoff_set.
      - apply old_expression_value; apply value_int.
      - handoff_route; apply store_done; reflexivity. }
    destruct OUTCOME as [[ENDPOINT DISTINCT]|[failure_k ENDPOINT]]; subst endpoint.
    + exists (11+aliascount)%nat,
        (State EntrySource.f_guest handoff_fd_format (Kseq handoff_descriptor_after_format k) e final m),final.
      split.
      * pose proof (Z2Nat.id index ltac:(lia)); lia.
      * split; [exact GUARDFRAME|]. split.
        -- eapply store_path_trans with (n:=9%nat); [exact START|].
           replace (S (S aliascount)) with (aliascount+2)%nat by lia.
           eapply store_path_trans with (n:=aliascount); [exact ALIASES|].
           handoff_route; rewrite handoff_descriptor_after_alias_actual at 1; handoff_route.
           apply store_done; reflexivity.
        -- left; auto.
    + exists (9+aliascount)%nat,
        (State EntrySource.f_guest handoff_descriptor_failure failure_k e final m),final.
      split.
      * pose proof (Z2Nat.id index ltac:(lia)); lia.
      * split; [exact GUARDFRAME|]. split.
        -- eapply store_path_trans; [exact START|exact ALIASES].
        -- right; eexists; reflexivity.
Qed.

Lemma handoff_descriptor_iterations_actual : handoff_descriptor_iterations =
  Sloop handoff_descriptor_body handoff_descriptor_increment.
Proof. reflexivity. Qed.
Lemma handoff_descriptor_test_actual : handoff_descriptor_test =
  Sifthenelse (Ebinop Olt (Etempvar EntrySource._i tuint) (Econst_int (Int.repr 4) tint) tint) Sskip Sbreak.
Proof. reflexivity. Qed.
Lemma handoff_descriptor_loop_actual : handoff_descriptor_loop =
  Ssequence (Sset EntrySource._i (Econst_int Int.zero tint)) handoff_descriptor_iterations.
Proof. reflexivity. Qed.

Lemma handoff_descriptor_test_operation ge m index : 0 <= index <= 4 ->
  sem_binary_operation ge Olt (Vint (Int.repr index)) tuint (Vint (Int.repr 4)) tint m =
    Some (Val.of_bool (index <? 4)).
Proof.
  intros BOUND; change (Some (Val.of_bool (Int.ltu (Int.repr index) (Int.repr 4))) =
    Some (Val.of_bool (index <? 4))).
  unfold Int.ltu; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  change (Some (Val.of_bool (if zlt index 4 then true else false)) = Some (Val.of_bool (index <? 4))).
  destruct (zlt index 4) as [LOW|HIGH].
  - rewrite (proj2 (Z.ltb_lt index 4) LOW); reflexivity.
  - rewrite (proj2 (Z.ltb_ge index 4) ltac:(lia)); reflexivity.
Qed.

Lemma handoff_descriptor_test_edge e le m k index :
  le ! EntrySource._i = Some (Vint (Int.repr index)) -> 0 <= index <= 4 ->
  store_edge handoff_ge (State EntrySource.f_guest handoff_descriptor_test k e le m)
    (State EntrySource.f_guest (if index <? 4 then Sskip else Sbreak) k e le m).
Proof.
  intros INDEX BOUND; rewrite handoff_descriptor_test_actual.
  apply certified_if_edge with (v:=Val.of_bool (index <? 4)).
  - eapply binary_expression_value.
    + apply old_expression_value; apply value_temp; exact INDEX.
    + apply old_expression_value; apply value_int.
    + apply handoff_descriptor_test_operation; exact BOUND.
  - apply NumberControl.number_bool_value.
Qed.

Lemma handoff_descriptor_iteration_source e le m k index :
  le ! EntrySource._i=Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  store_path handoff_ge (fun after=>after=m)
    (State EntrySource.f_guest handoff_descriptor_iterations k e le m) 5
    (State EntrySource.f_guest handoff_descriptor_range
      (Kseq handoff_descriptor_after_range (Kloop1 handoff_descriptor_body handoff_descriptor_increment k)) e le m).
Proof.
  intros INDEX BOUND; rewrite handoff_descriptor_iterations_actual at 1; handoff_route.
  rewrite handoff_descriptor_body_actual at 1; handoff_route.
  eapply store_next; [reflexivity|apply handoff_descriptor_test_edge with (index:=index); [exact INDEX|lia]|].
  rewrite (proj2 (Z.ltb_lt index 4) ltac:(lia)); handoff_route.
  handoff_route; apply store_done; reflexivity.
Qed.

Lemma handoff_descriptor_exit_source e le m k :
  le ! EntrySource._i=Some (Vint (Int.repr 4)) ->
  store_path handoff_ge (fun after=>after=m)
    (State EntrySource.f_guest handoff_descriptor_iterations k e le m) 5
    (State EntrySource.f_guest Sskip k e le m).
Proof.
  intros INDEX; rewrite handoff_descriptor_iterations_actual at 1; handoff_route.
  rewrite handoff_descriptor_body_actual at 1; handoff_route.
  eapply store_next; [reflexivity|apply handoff_descriptor_test_edge with (index:=4); [exact INDEX|lia]|].
  cbn [Z.ltb]; handoff_route; handoff_route; apply store_done; reflexivity.
Qed.

Lemma handoff_descriptor_increment_source e le m k index :
  le ! EntrySource._i=Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  store_path handoff_ge (fun after=>after=m)
    (State EntrySource.f_guest Sskip (Kloop1 handoff_descriptor_body handoff_descriptor_increment k) e le m) 3
    (State EntrySource.f_guest handoff_descriptor_iterations k e
      (PTree.set EntrySource._i (Vint (Int.repr (index+1))) le) m).
Proof.
  intros INDEX BOUND; handoff_route.
  eapply store_next; [reflexivity|apply certified_set_edge with (v:=Vint (Int.repr (index+1)))|].
  - eapply binary_expression_value.
    + apply old_expression_value; apply value_temp; exact INDEX.
    + apply old_expression_value; apply value_int.
    + change (Some (Vint (Int.add (Int.repr index) Int.one)) = Some (Vint (Int.repr (index+1)))).
      unfold Int.add; change (Some (Vint (Int.repr (Int.unsigned (Int.repr index)+1))) =
        Some (Vint (Int.repr (index+1)))).
      rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia); reflexivity.
  - handoff_route; apply store_done; reflexivity.
Qed.
