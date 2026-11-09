(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual owned pointer-table loads and stores in the guest handoff. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Errors Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ScalarMemory.
From EntryNative Require Import EntrySource NativeHandoffStructure.
From LeanCageMainNumber Require Import NumberInitial NumberControl.
From LeanCageMain Require Import MainFields.
Import ListNotations.
Open Scope Z_scope.

Definition handoff_ge := Clight.globalenv EntrySource.prog.
Definition handoff_symbol id :=
  match Genv.find_symbol handoff_ge id with Some block => block | None => 1%positive end.

Lemma handoff_policy_binding :
  Genv.find_symbol handoff_ge EntrySource._policy__1 = Some (handoff_symbol EntrySource._policy__1).
Proof. reflexivity. Qed.

Lemma handoff_policy_arguments_location e le m : e ! EntrySource._policy__1 = None ->
  location_value handoff_ge e le m guest_argument_source
    (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88).
Proof.
  intros GLOBAL.
  assert (LAYOUT : exists co, (genv_cenv handoff_ge) ! EntrySource._policy = Some co /\
    field_offset handoff_ge EntrySource._args (co_members co) = OK (88,Full)).
  { apply field_lookup_sound; vm_compute; reflexivity. }
  destruct LAYOUT as [co [CO FIELD]].
  replace (Ptrofs.repr 88) with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 88))
    by (rewrite Ptrofs.add_zero_l; reflexivity).
  unfold guest_argument_source; eapply struct_location_value.
  - eapply location_read_value; [apply global_location_value; [exact GLOBAL|apply handoff_policy_binding]|].
    apply deref_loc_copy; reflexivity.
  - reflexivity.
  - exact CO.
  - exact FIELD.
Qed.

Lemma handoff_policy_arguments_value e le m block offset :
  e ! EntrySource._policy__1 = None ->
  Mem.loadv Mptr m (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) = Some (Vptr block offset) ->
  expression_value handoff_ge e le m guest_argument_source (Vptr block offset).
Proof.
  intros GLOBAL LOAD; eapply location_read_value; [apply handoff_policy_arguments_location; exact GLOBAL|].
  eapply deref_loc_value; [reflexivity|exact LOAD].
Qed.

Lemma handoff_array_value ge e le m id ty count block :
  e ! id = Some (block,tarray ty count) ->
  expression_value ge e le m (Evar id (tarray ty count)) (Vptr block Ptrofs.zero).
Proof.
  intros LOCAL; eapply location_read_value; [apply local_location_value; exact LOCAL|].
  apply deref_loc_reference; reflexivity.
Qed.

Lemma handoff_pointer_add_long ge m block offset index : 0 <= index <= 74 ->
  sem_binary_operation ge Oadd (Vptr block offset) (tptr (tptr tschar))
    (Vlong (Int64.repr index)) tulong m =
  Some (Vptr block (Ptrofs.add offset (Ptrofs.repr (8 * index)))).
Proof.
  intros INDEX.
  change (Some (Vptr block (Ptrofs.add offset
    (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr index))))) =
    Some (Vptr block (Ptrofs.add offset (Ptrofs.repr (8 * index))))).
  unfold Ptrofs.of_int64;
    rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  rewrite Ptrofs.mul_signed.
  rewrite !Ptrofs.signed_repr by
    (change Ptrofs.min_signed with (-9223372036854775808);
     change Ptrofs.max_signed with 9223372036854775807; lia).
  reflexivity.
Qed.

Lemma handoff_pointer_add_array ge m block index : 0 <= index <= 74 ->
  sem_binary_operation ge Oadd (Vptr block Ptrofs.zero) (tarray (tptr tschar) 74)
    (Vlong (Int64.repr index)) tulong m = Some (Vptr block (Ptrofs.repr (8 * index))).
Proof.
  intros INDEX.
  change (sem_binary_operation ge Oadd (Vptr block Ptrofs.zero) (tptr (tptr tschar))
    (Vlong (Int64.repr index)) tulong m = Some (Vptr block (Ptrofs.repr (8 * index)))).
  rewrite handoff_pointer_add_long by exact INDEX; rewrite Ptrofs.add_zero_l; reflexivity.
Qed.

Lemma handoff_index_increment ge m index : 0 <= index <= 64 ->
  sem_binary_operation ge Oadd (Vlong (Int64.repr index)) tulong
    (Vint (Int.repr 1)) tint m = Some (Vlong (Int64.repr (index + 1))).
Proof.
  intros INDEX.
  change (Some (Vlong (Int64.add (Int64.repr index) Int64.one)) =
    Some (Vlong (Int64.repr (index + 1)))).
  unfold Int64.add.
  change (Some (Vlong (Int64.repr (Int64.unsigned (Int64.repr index) + 1))) =
    Some (Vlong (Int64.repr (index + 1)))).
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia); reflexivity.
Qed.

Lemma handoff_index_destination ge m index : 0 <= index <= 64 ->
  sem_binary_operation ge Oadd (Vint (Int.repr 9)) tint
    (Vlong (Int64.repr index)) tulong m = Some (Vlong (Int64.repr (9 + index))).
Proof.
  intros INDEX.
  change (Some (Vlong (Int64.add (Int64.repr 9) (Int64.repr index))) =
    Some (Vlong (Int64.repr (9 + index)))).
  unfold Int64.add.
  change (Some (Vlong (Int64.repr (9 + Int64.unsigned (Int64.repr index)))) =
    Some (Vlong (Int64.repr (9 + index)))).
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia); reflexivity.
Qed.

Lemma handoff_index_test ge m index : 0 <= index <= 64 ->
  sem_binary_operation ge Olt (Vlong (Int64.repr index)) tulong
    (Vint (Int.repr 64)) tint m = Some (Val.of_bool (index <? 64)).
Proof.
  intros INDEX.
  change (Some (Val.of_bool (Int64.ltu (Int64.repr index) (Int64.repr 64))) =
    Some (Val.of_bool (index <? 64))).
  unfold Int64.ltu; rewrite (Int64.unsigned_repr index)
    by (change Int64.max_unsigned with 18446744073709551615; lia).
  change (Some (Val.of_bool (if zlt index 64 then true else false)) =
    Some (Val.of_bool (index <? 64))).
  destruct (zlt index 64).
  - rewrite (proj2 (Z.ltb_lt index 64) ltac:(lia)); reflexivity.
  - rewrite (proj2 (Z.ltb_ge index 64) ltac:(lia)); reflexivity.
Qed.

Fixpoint handoff_pointer_cells (index : Z) (values : list val) : list scalar_cell :=
  match values with
  | [] => []
  | value :: rest => {|scalar_chunk := Mptr; scalar_offset := 8 * index; scalar_value := value|}
      :: handoff_pointer_cells (index + 1) rest
  end.

Definition handoff_pointer_stores block index before values after :=
  scalar_stores block before (handoff_pointer_cells index values) after.

Definition handoff_pointer_prefix block index before values after :=
  exists written rest, values = written ++ rest /\ handoff_pointer_stores block index before written after.

Lemma handoff_pointer_prefix_initial block index before values :
  handoff_pointer_prefix block index before values before.
Proof. exists [],values; split; [reflexivity|constructor]. Qed.

Lemma handoff_pointer_prefix_cons block index before value values middle after :
  Mem.store Mptr before block (8 * index) value = Some middle ->
  handoff_pointer_prefix block (index + 1) middle values after ->
  handoff_pointer_prefix block index before (value :: values) after.
Proof.
  intros STORE [written [rest [VALUES STORES]]].
  exists (value :: written),rest; split; [cbn; congruence|]. econstructor; eassumption.
Qed.

Lemma handoff_pointer_stores_load_other block index before values after other chunk offset :
  handoff_pointer_stores block index before values after -> other <> block ->
  Mem.loadv chunk after (Vptr other offset) = Mem.loadv chunk before (Vptr other offset).
Proof.
  intros STORES DIFFERENT; unfold Mem.loadv; destruct (zle _ _); [|reflexivity].
  eapply scalar_stores_load_other; [exact STORES|left; exact DIFFERENT].
Qed.

Lemma handoff_argument_slot_value e le m source offset index loaded value :
  le ! loaded = Some (Vptr source offset) ->
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) ->
  0 <= index <= 64 ->
  Mem.loadv Mptr m (Vptr source (Ptrofs.add offset (Ptrofs.repr (8 * index)))) = Some value ->
  expression_value handoff_ge e le m
    (Ederef (Ebinop Oadd (Etempvar loaded (tptr (tptr tschar)))
      (Etempvar EntrySource._i__2 tulong) (tptr (tptr tschar))) (tptr tschar)) value.
Proof.
  intros SOURCE INDEX BOUND LOAD.
  eapply location_read_value.
  - apply pointer_location_value; eapply binary_expression_value.
    + apply old_expression_value; apply value_temp; exact SOURCE.
    + apply old_expression_value; apply value_temp; exact INDEX.
    + apply handoff_pointer_add_long; lia.
  - eapply deref_loc_value; [reflexivity|exact LOAD].
Qed.

Definition handoff_copy_guard_env le source offset value (proceed : bool) :=
  PTree.set EntrySource._t'20 (Val.of_bool proceed)
    (PTree.set EntrySource._t'28 value
      (PTree.set EntrySource._t'27 (Vptr source offset) le)).

Ltac handoff_route := eapply store_next; [reflexivity|apply unchanged_store_edge; WriteAll.structural|].
Ltac handoff_set := eapply store_next; [reflexivity|apply certified_set_edge|].

Theorem handoff_copy_guard_pointer_source e le m source offset index argument argument_offset k :
  e ! EntrySource._policy__1 = None ->
  Mem.loadv Mptr m (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) = Some (Vptr source offset) ->
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) -> 0 <= index < 64 ->
  Mem.loadv Mptr m (Vptr source (Ptrofs.add offset (Ptrofs.repr (8 * index)))) =
    Some (Vptr argument argument_offset) ->
  Mem.weak_valid_pointer m argument (Ptrofs.unsigned argument_offset) = true ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest guest_copy_test k e le m) 11
    (State EntrySource.f_guest Sskip k e
      (handoff_copy_guard_env le source offset (Vptr argument argument_offset) true) m).
Proof.
  intros GLOBAL POLICY INDEX BOUND LOAD LIVE.
  unfold guest_copy_test, guest_copy_body; rewrite guest_argument_copy_actual; cbn.
  handoff_route; handoff_route.
  handoff_set.
  - apply handoff_policy_arguments_value; [exact GLOBAL|exact POLICY].
  - handoff_route; handoff_route.
    handoff_set.
    + apply handoff_argument_slot_value with (source := source) (offset := offset) (index := index).
      * apply PTree.gss.
      * WriteAll.lookup.
      * lia.
      * exact LOAD.
    + handoff_route.
      eapply store_next; [reflexivity|apply certified_if_edge with
        (v := Vptr argument argument_offset) (b := true)|].
      * apply old_expression_value; apply value_temp; apply PTree.gss.
      * change ((if Mem.weak_valid_pointer m argument (Ptrofs.unsigned argument_offset)
          then Some true else None) = Some true); rewrite LIVE; reflexivity.
      * handoff_set.
        -- eapply cast_expression_value.
           ++ eapply binary_expression_value.
              ** apply old_expression_value; apply value_temp; WriteAll.lookup.
              ** apply old_expression_value; apply value_int.
              ** rewrite handoff_index_test by lia.
                 rewrite (proj2 (Z.ltb_lt index 64) ltac:(lia)); reflexivity.
           ++ reflexivity.
        -- handoff_route.
           eapply store_next; [reflexivity|apply certified_if_edge with
             (v := Val.of_bool true) (b := true)|].
           ++ apply old_expression_value; apply value_temp; apply PTree.gss.
           ++ reflexivity.
           ++ apply store_done; reflexivity.
Qed.

Theorem handoff_copy_guard_null_source e le m source offset index k :
  e ! EntrySource._policy__1 = None ->
  Mem.loadv Mptr m (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) = Some (Vptr source offset) ->
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) -> 0 <= index <= 64 ->
  Mem.loadv Mptr m (Vptr source (Ptrofs.add offset (Ptrofs.repr (8 * index)))) = Some (Vlong Int64.zero) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest guest_copy_test k e le m) 11
    (State EntrySource.f_guest Sbreak k e
      (handoff_copy_guard_env le source offset (Vlong Int64.zero) false) m).
Proof.
  intros GLOBAL POLICY INDEX BOUND LOAD.
  unfold guest_copy_test, guest_copy_body; rewrite guest_argument_copy_actual; cbn.
  handoff_route; handoff_route.
  handoff_set.
  - apply handoff_policy_arguments_value; [exact GLOBAL|exact POLICY].
  - handoff_route; handoff_route.
    handoff_set.
    + apply handoff_argument_slot_value with (source := source) (offset := offset) (index := index).
      * apply PTree.gss.
      * WriteAll.lookup.
      * exact BOUND.
      * exact LOAD.
    + handoff_route.
      eapply store_next; [reflexivity|apply certified_if_edge with
        (v := Vlong Int64.zero) (b := false)|].
      * apply old_expression_value; apply value_temp; apply PTree.gss.
      * reflexivity.
      * handoff_set.
        -- apply old_expression_value; apply value_int.
        -- handoff_route.
           eapply store_next; [reflexivity|apply certified_if_edge with
             (v := Val.of_bool false) (b := false)|].
           ++ apply old_expression_value; apply value_temp; apply PTree.gss.
           ++ reflexivity.
           ++ apply store_done; reflexivity.
Qed.

Definition handoff_copy_store_env le source offset value :=
  PTree.set EntrySource._t'26 value (PTree.set EntrySource._t'25 (Vptr source offset) le).

Theorem handoff_copy_store_source e le before after source offset index output argument argument_offset k :
  e ! EntrySource._policy__1 = None ->
  e ! EntrySource._args = Some (output,tarray (tptr tschar) 74) ->
  Mem.loadv Mptr before (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) = Some (Vptr source offset) ->
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) -> 0 <= index < 64 ->
  Mem.loadv Mptr before (Vptr source (Ptrofs.add offset (Ptrofs.repr (8 * index)))) =
    Some (Vptr argument argument_offset) ->
  Mem.store Mptr before output (8 * (9 + index)) (Vptr argument argument_offset) = Some after ->
  store_path handoff_ge (fun current => current = before \/ current = after)
    (State EntrySource.f_guest guest_copy_store k e le before) 7
    (State EntrySource.f_guest Sskip k e
      (handoff_copy_store_env le source offset (Vptr argument argument_offset)) after).
Proof.
  intros GLOBAL LOCAL POLICY INDEX BOUND LOAD STORE.
  unfold guest_copy_store, guest_copy_body; rewrite guest_argument_copy_actual; cbn.
  eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [left; reflexivity|apply certified_set_edge|].
  - apply handoff_policy_arguments_value; [exact GLOBAL|exact POLICY].
  - eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
    eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
    eapply store_next; [left; reflexivity|apply certified_set_edge|].
    + apply handoff_argument_slot_value with (source := source) (offset := offset) (index := index).
      * apply PTree.gss.
      * WriteAll.lookup.
      * lia.
      * exact LOAD.
    + eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
      eapply store_next; [left; reflexivity| |].
      * eapply assignment_source_edge with (v := Vptr argument argument_offset) (w := Vptr argument argument_offset).
        -- apply pointer_location_value; eapply binary_expression_value.
           ++ apply handoff_array_value; exact LOCAL.
           ++ eapply binary_expression_value.
              ** apply old_expression_value; apply value_int.
              ** apply old_expression_value; apply value_temp; WriteAll.lookup.
              ** apply handoff_index_destination; lia.
           ++ apply handoff_pointer_add_array; lia.
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- reflexivity.
        -- eapply assign_loc_value; [reflexivity|].
           unfold Mem.storev; rewrite Ptrofs.unsigned_repr
             by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
           destruct (zle _ _) as [LIMIT|OVER]; [exact STORE|].
           exfalso; change (8 * (9 + index) + 8 > 18446744073709551616) in OVER; lia.
      * apply store_done; right; reflexivity.
Qed.


Definition handoff_argument_pointer := (block * Ptrofs.int)%type.
Definition handoff_argument_value (pointer : handoff_argument_pointer) := Vptr (fst pointer) (snd pointer).

Fixpoint handoff_copy_inputs m source offset index (arguments : list handoff_argument_pointer) : Prop :=
  match arguments with
  | [] => Mem.loadv Mptr m (Vptr source (Ptrofs.add offset (Ptrofs.repr (8 * index)))) = Some (Vlong Int64.zero)
  | pointer :: rest =>
      Mem.loadv Mptr m (Vptr source (Ptrofs.add offset (Ptrofs.repr (8 * index)))) = Some (handoff_argument_value pointer) /\
      Mem.weak_valid_pointer m (fst pointer) (Ptrofs.unsigned (snd pointer)) = true /\
      handoff_copy_inputs m source offset (index + 1) rest
  end.

Lemma handoff_store_valid_pointer chunk before output position value after block offset :
  Mem.store chunk before output position value = Some after ->
  Mem.valid_pointer after block offset = Mem.valid_pointer before block offset.
Proof.
  intros STORE.
  assert (SAME : Mem.valid_pointer after block offset = true <-> Mem.valid_pointer before block offset = true).
  { rewrite !Mem.valid_pointer_nonempty_perm; split; eauto using Mem.perm_store_1, Mem.perm_store_2. }
  destruct (Mem.valid_pointer after block offset), (Mem.valid_pointer before block offset); intuition congruence.
Qed.

Lemma handoff_store_weak_pointer chunk before output position value after block offset :
  Mem.store chunk before output position value = Some after ->
  Mem.weak_valid_pointer after block offset = Mem.weak_valid_pointer before block offset.
Proof.
  intros STORE; unfold Mem.weak_valid_pointer.
  rewrite (handoff_store_valid_pointer _ _ _ _ _ _ _ _ STORE),
    (handoff_store_valid_pointer _ _ _ _ _ _ _ _ STORE); reflexivity.
Qed.

Lemma handoff_store_loadv_other chunk before output position value after block offset :
  Mem.store chunk before output position value = Some after -> block <> output ->
  Mem.loadv Mptr after (Vptr block offset) = Mem.loadv Mptr before (Vptr block offset).
Proof.
  intros STORE DIFFERENT; unfold Mem.loadv; destruct (zle _ _); [|reflexivity].
  eapply Mem.load_store_other; [exact STORE|left; exact DIFFERENT].
Qed.

Lemma handoff_copy_inputs_store before output position value after source offset index arguments :
  Mem.store Mptr before output position value = Some after -> source <> output ->
  handoff_copy_inputs before source offset index arguments ->
  handoff_copy_inputs after source offset index arguments.
Proof.
  intros STORE DIFFERENT; revert index; induction arguments as [|pointer rest IH];
    intros index INPUTS; cbn [handoff_copy_inputs] in *.
  - rewrite (handoff_store_loadv_other _ _ _ _ _ _ _ _ STORE DIFFERENT); exact INPUTS.
  - destruct INPUTS as [LOAD [LIVE TAIL]].
    rewrite (handoff_store_loadv_other _ _ _ _ _ _ _ _ STORE DIFFERENT),
      (handoff_store_weak_pointer _ _ _ _ _ _ _ _ STORE).
    split; [exact LOAD|]. split; [exact LIVE|apply IH; exact TAIL].
Qed.

Definition handoff_copy_advanced le source offset pointer index :=
  PTree.set EntrySource._i__2 (Vlong (Int64.repr (index + 1)))
    (handoff_copy_store_env
      (handoff_copy_guard_env le source offset (handoff_argument_value pointer) true)
      source offset (handoff_argument_value pointer)).

Lemma handoff_copy_advance_source e le m source offset pointer index k :
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) -> 0 <= index < 64 ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest guest_copy_increment k e
      (handoff_copy_store_env
        (handoff_copy_guard_env le source offset (handoff_argument_value pointer) true)
        source offset (handoff_argument_value pointer)) m) 1
    (State EntrySource.f_guest Sskip k e (handoff_copy_advanced le source offset pointer index) m).
Proof.
  intros INDEX BOUND; unfold guest_copy_increment, guest_copy_body;
    rewrite guest_argument_copy_actual; cbn.
  handoff_set.
  - eapply binary_expression_value.
    + apply old_expression_value; apply value_temp; unfold handoff_copy_store_env, handoff_copy_guard_env; WriteAll.lookup.
    + apply old_expression_value; apply value_int.
    + apply handoff_index_increment; lia.
  - apply store_done; reflexivity.
Qed.

Definition handoff_copy_loop_cont k := Kloop1 guest_copy_body Sskip k.
Definition handoff_copy_guard_cont k :=
  Kseq (Ssequence guest_copy_store guest_copy_increment) (handoff_copy_loop_cont k).

Theorem handoff_copy_loop_source_bounded e le before after source offset index output arguments k failure :
  e ! EntrySource._policy__1 = None ->
  e ! EntrySource._args = Some (output,tarray (tptr tschar) 74) ->
  source <> output -> handoff_symbol EntrySource._policy__1 <> output ->
  Mem.loadv Mptr before (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) = Some (Vptr source offset) ->
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) ->
  le ! EntrySource._failure = Some (Vint failure) ->
  0 <= index -> index + Z.of_nat (length arguments) <= 64 ->
  handoff_copy_inputs before source offset index arguments ->
  handoff_pointer_stores output (9 + index) before (map handoff_argument_value arguments) after ->
  exists count final,
    (count <= 26 * length arguments + 15)%nat /\
    final ! EntrySource._i__2 = Some (Vlong (Int64.repr (index + Z.of_nat (length arguments)))) /\
    final ! EntrySource._failure = Some (Vint failure) /\
    store_path handoff_ge
      (handoff_pointer_prefix output (9 + index) before (map handoff_argument_value arguments))
      (State EntrySource.f_guest guest_copy_arguments k e le before) count
      (State EntrySource.f_guest Sskip k e final after).
Proof.
  revert before index le; induction arguments as [|[argument argument_offset] rest IH];
    intros before index le GLOBAL LOCAL SOURCE DIFFERENT POLICY INDEX FAILURE LOW HIGH INPUTS STORES.
  - inversion STORES; subst after.
    exists 15%nat, (handoff_copy_guard_env le source offset (Vlong Int64.zero) false).
    split; [cbn [length]; lia|].
    split; [cbn [length Z.of_nat]; rewrite Z.add_0_r; unfold handoff_copy_guard_env; WriteAll.lookup|].
    split; [unfold handoff_copy_guard_env; WriteAll.lookup|].
    eapply number_path_implication with (P := fun current => current = before).
    { intros current SAME; subst; apply handoff_pointer_prefix_initial. }
    rewrite guest_copy_loop_structure; eapply store_path_trans with (n := 2%nat).
    + handoff_route; rewrite guest_copy_body_structure; handoff_route; apply store_done; reflexivity.
    + eapply store_path_trans with (n := 11%nat).
      * apply handoff_copy_guard_null_source with (source := source) (offset := offset) (index := index);
          try assumption; cbn [length Z.of_nat] in HIGH; lia.
      * handoff_route; handoff_route; apply store_done; reflexivity.
  - cbn [length map handoff_copy_inputs] in INPUTS, STORES, HIGH |- *.
    destruct INPUTS as [LOAD [LIVE INPUTS]].
    inversion STORES as [|? ? ? middle ? STORE TAIL]; subst.
    assert (BOUND : 0 <= index < 64) by (rewrite Nat2Z.inj_succ in HIGH; lia).
    assert (NEXTINPUTS : handoff_copy_inputs middle source offset (index + 1) rest).
    { eapply handoff_copy_inputs_store; [exact STORE|exact SOURCE|exact INPUTS]. }
    assert (NEXTPOLICY : Mem.loadv Mptr middle
      (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) = Some (Vptr source offset)).
    { rewrite (handoff_store_loadv_other _ _ _ _ _ _ _ _ STORE DIFFERENT); exact POLICY. }
    set (advanced := handoff_copy_advanced le source offset (argument,argument_offset) index).
    destruct (IH middle (index + 1) advanced GLOBAL LOCAL SOURCE DIFFERENT NEXTPOLICY
      ltac:(unfold advanced, handoff_copy_advanced; apply PTree.gss)
      ltac:(unfold advanced, handoff_copy_advanced, handoff_copy_store_env, handoff_copy_guard_env; WriteAll.lookup)
      ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in HIGH; lia) NEXTINPUTS
      ltac:(replace (9 + (index + 1)) with (9 + index + 1) by lia; exact TAIL))
      as [count [final [COUNTBOUND [FINALINDEX [FINALFAILURE PATH]]]]].
    exists (26 + count)%nat, final; split; [cbn [length]; lia|]. split.
    + rewrite Nat2Z.inj_succ; replace (index + Z.succ (Z.of_nat (length rest)))
        with (index + 1 + Z.of_nat (length rest)) by lia; exact FINALINDEX.
    + split; [exact FINALFAILURE|].
      assert (START : handoff_pointer_prefix output (9 + index) before
        (handoff_argument_value (argument,argument_offset) :: map handoff_argument_value rest) before)
        by apply handoff_pointer_prefix_initial.
      assert (MID : handoff_pointer_prefix output (9 + index) before
        (handoff_argument_value (argument,argument_offset) :: map handoff_argument_value rest) middle).
      { apply handoff_pointer_prefix_cons with (middle := middle); [exact STORE|apply handoff_pointer_prefix_initial]. }
      rewrite guest_copy_loop_structure.
      eapply store_path_trans with (n := 2%nat).
      * eapply store_next; [exact START|apply unchanged_store_edge; WriteAll.structural|].
        rewrite guest_copy_body_structure.
        eapply store_next; [exact START|apply unchanged_store_edge; WriteAll.structural|].
        apply store_done; exact START.
      * eapply store_path_trans with (n := 11%nat).
        -- eapply number_path_implication with (P := fun current => current = before).
           ++ intros current SAME; subst; exact START.
           ++ apply handoff_copy_guard_pointer_source with (source := source) (offset := offset) (index := index)
                (argument := argument) (argument_offset := argument_offset);
                try assumption.
        -- eapply store_path_trans with (n := 2%nat).
           ++ eapply store_next; [exact START|apply unchanged_store_edge; WriteAll.structural|].
              eapply store_next; [exact START|apply unchanged_store_edge; WriteAll.structural|].
              apply store_done; exact START.
           ++ eapply store_path_trans with (n := 7%nat).
              ** eapply number_path_implication with (P := fun current => current = before \/ current = middle).
                 --- intros current [SAME|SAME]; subst; [exact START|exact MID].
                 --- apply handoff_copy_store_source with (source := source) (offset := offset) (index := index)
                      (output := output) (argument := argument) (argument_offset := argument_offset);
                      try assumption; unfold handoff_copy_guard_env; WriteAll.lookup.
              ** eapply store_path_trans with (n := 4%nat).
                 --- eapply store_next; [exact MID|apply unchanged_store_edge; WriteAll.structural|].
                     eapply store_path_trans with (n := 1%nat).
                     +++ eapply number_path_implication with (P := fun current => current = middle).
                         *** intros current SAME; subst; exact MID.
                         *** apply handoff_copy_advance_source with (le := le) (source := source)
                               (offset := offset) (pointer := (argument,argument_offset)) (index := index);
                               assumption.
                     +++ eapply store_next; [exact MID|apply unchanged_store_edge; WriteAll.structural|].
                         eapply store_next; [exact MID|apply unchanged_store_edge; WriteAll.structural|].
                         apply store_done; exact MID.
                 --- eapply number_path_implication; [|exact PATH].
                     intros current PREFIX.
                     apply handoff_pointer_prefix_cons with (middle := middle); [exact STORE|].
                     replace (9 + index + 1) with (9 + (index + 1)) by lia; exact PREFIX.
Qed.

Theorem handoff_copy_loop_source e le before after source offset index output arguments k failure :
  e ! EntrySource._policy__1 = None ->
  e ! EntrySource._args = Some (output,tarray (tptr tschar) 74) ->
  source <> output -> handoff_symbol EntrySource._policy__1 <> output ->
  Mem.loadv Mptr before (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) = Some (Vptr source offset) ->
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) ->
  le ! EntrySource._failure = Some (Vint failure) ->
  0 <= index -> index + Z.of_nat (length arguments) <= 64 ->
  handoff_copy_inputs before source offset index arguments ->
  handoff_pointer_stores output (9 + index) before (map handoff_argument_value arguments) after ->
  exists count final,
    final ! EntrySource._i__2 = Some (Vlong (Int64.repr (index + Z.of_nat (length arguments)))) /\
    final ! EntrySource._failure = Some (Vint failure) /\
    store_path handoff_ge
      (handoff_pointer_prefix output (9 + index) before (map handoff_argument_value arguments))
      (State EntrySource.f_guest guest_copy_arguments k e le before) count
      (State EntrySource.f_guest Sskip k e final after).
Proof.
  intros GLOBAL LOCAL SOURCE DIFFERENT POLICY INDEX FAILURE LOW HIGH INPUTS STORES.
  destruct(handoff_copy_loop_source_bounded e le before after source offset index output arguments k failure
    GLOBAL LOCAL SOURCE DIFFERENT POLICY INDEX FAILURE LOW HIGH INPUTS STORES)
    as[count[final[BOUND REST]]].
  exists count,final;exact REST.
Qed.

Lemma handoff_pointer_cells_valid index values :
  0 <= index -> index + Z.of_nat (length values) <= 74 ->
  Forall (scalar_valid 592) (handoff_pointer_cells index values).
Proof.
  revert index; induction values as [|value rest IH]; intros index LOW HIGH; cbn [handoff_pointer_cells]; [constructor|].
  constructor.
  - change (0 <= 8 * index /\ 8 * index + 8 <= 592 /\ (8 | 8 * index)).
    cbn [length] in HIGH; rewrite Nat2Z.inj_succ in HIGH.
    split; [lia|]. split; [lia|exists index; ring].
  - apply IH; [lia|]. cbn [length] in HIGH; rewrite Nat2Z.inj_succ in HIGH; lia.
Qed.

Theorem handoff_pointer_stores_exist block index before values :
  0 <= index -> index + Z.of_nat (length values) <= 74 ->
  Mem.range_perm before block 0 592 Cur Freeable ->
  exists after, handoff_pointer_stores block index before values after.
Proof.
  intros LOW HIGH OWN; apply scalar_stores_exist with (size := 592);
    [apply handoff_pointer_cells_valid; assumption|exact OWN].
Qed.

Lemma handoff_pointer_cells_lower index values :
  Forall (fun cell => 8 * index <= scalar_offset cell) (handoff_pointer_cells index values).
Proof.
  revert index; induction values as [|value rest IH]; intros index; cbn [handoff_pointer_cells]; [constructor|].
  constructor; [cbn; lia|].
  eapply Forall_impl with (P := fun cell => 8 * (index + 1) <= scalar_offset cell).
  - intros cell LOW; lia.
  - apply IH.
Qed.

Lemma handoff_pointer_cells_ordered index values :
  forall before cell rest, handoff_pointer_cells index values = before ++ cell :: rest ->
    Forall (scalar_separate cell) rest.
Proof.
  revert index; induction values as [|value values IH]; intros index before cell rest EQUATION.
  - destruct before; discriminate.
  - destruct before as [|first before].
    + cbn [app handoff_pointer_cells] in EQUATION; inversion EQUATION; subst.
      eapply Forall_impl with (P := fun later => 8 * (index + 1) <= scalar_offset later).
      * intros later LOW; left; change (8 * index + 8 <= scalar_offset later); lia.
      * apply handoff_pointer_cells_lower.
    + cbn [app handoff_pointer_cells] in EQUATION; inversion EQUATION.
      eapply IH; eassumption.
Qed.

Lemma handoff_pointer_cell_present index values item position :
  nth_error values position = Some item ->
  In {|scalar_chunk := Mptr; scalar_offset := 8 * (index + Z.of_nat position); scalar_value := item|}
    (handoff_pointer_cells index values).
Proof.
  revert index position; induction values as [|value rest IH]; intros index position FOUND;
    destruct position as [|position]; cbn [nth_error] in FOUND; try discriminate.
  - inversion FOUND; subst item; cbn [handoff_pointer_cells Z.of_nat]; rewrite Z.add_0_r; left; reflexivity.
  - cbn [handoff_pointer_cells]; right; rewrite Nat2Z.inj_succ.
    replace (index + Z.succ (Z.of_nat position)) with (index + 1 + Z.of_nat position) by lia.
    apply IH; exact FOUND.
Qed.

Theorem handoff_pointer_stores_content block index before values after position item :
  handoff_pointer_stores block index before values after ->
  nth_error values position = Some item ->
  Mem.load Mptr after block (8 * (index + Z.of_nat position)) = Some (Val.load_result Mptr item).
Proof.
  intros STORES FOUND.
  exact (scalar_stores_fields _ _ _ _ STORES (handoff_pointer_cells_ordered index values)
    _ (handoff_pointer_cell_present index values item position FOUND)).
Qed.
