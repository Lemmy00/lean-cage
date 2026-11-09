(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Construct the actual worker argument prefix in owned pointer slots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ScalarMemory.
From EntryNative Require Import EntrySource NativeHandoffStructure NativeHandoffArguments NativeHandoffAllocation.
From LeanCageMainNumber Require Import NumberInitial NumberControl.
Import ListNotations.
Open Scope Z_scope.

Definition handoff_args_frame output before after :=
  Mem.unchanged_on (fun object _ => object <> output) before after.

Lemma handoff_args_frame_refl output before : handoff_args_frame output before before.
Proof. apply Mem.unchanged_on_refl. Qed.

Lemma handoff_args_store_frame output base before after offset value :
  handoff_args_frame output base before -> Mem.store Mptr before output offset value = Some after ->
  handoff_args_frame output base after.
Proof.
  intros FRAME STORE; eapply Mem.unchanged_on_trans; [exact FRAME|].
  eapply Mem.store_unchanged_on; [exact STORE|]. intros i RANGE DIFFERENT; apply DIFFERENT; reflexivity.
Qed.

Lemma handoff_args_frame_loadv output before after object offset chunk value :
  handoff_args_frame output before after -> object <> output ->
  Mem.loadv chunk before (Vptr object offset) = Some value ->
  Mem.loadv chunk after (Vptr object offset) = Some value.
Proof.
  intros FRAME DIFFERENT LOAD; unfold Mem.loadv in *; destruct (zle _ _); [|discriminate].
  eapply Mem.load_unchanged_on; [exact FRAME| |exact LOAD]. intros i RANGE; exact DIFFERENT.
Qed.

Lemma handoff_prefix_pointer_add ge m block ty count size index si :
  sizeof ge ty = size -> 0 <= size <= 32 -> 0 <= index <= 74 ->
  sem_binary_operation ge Oadd (Vptr block Ptrofs.zero) (tarray ty count)
    (Vint (Int.repr index)) (Tint I32 si noattr) m =
  Some (Vptr block (Ptrofs.repr (size * index))).
Proof.
  intros SIZE STRIDE INDEX.
  change (Some (Vptr block (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr (sizeof ge ty)) (ptrofs_of_int si (Int.repr index))))) =
    Some (Vptr block (Ptrofs.repr (size * index)))).
  rewrite SIZE, Ptrofs.add_zero_l.
  unfold ptrofs_of_int; destruct si; unfold Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int.
  - rewrite Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
    rewrite Ptrofs.mul_signed, !Ptrofs.signed_repr by
      (change Ptrofs.min_signed with (-9223372036854775808); change Ptrofs.max_signed with 9223372036854775807; lia).
    reflexivity.
  - rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    rewrite Ptrofs.mul_signed, !Ptrofs.signed_repr by
      (change Ptrofs.min_signed with (-9223372036854775808); change Ptrofs.max_signed with 9223372036854775807; lia).
    reflexivity.
Qed.

Definition handoff_table_slot index :=
  Ederef (Ebinop Oadd (Evar EntrySource._args (tarray (tptr tschar) 74))
    (Econst_int (Int.repr index) tint) (tptr (tptr tschar))) (tptr tschar).

Lemma handoff_table_slot_location e le m output index :
  e ! EntrySource._args = Some (output,tarray (tptr tschar) 74) -> 0 <= index <= 73 ->
  location_value handoff_ge e le m (handoff_table_slot index) output (Ptrofs.repr (8 * index)).
Proof.
  intros LOCAL BOUND; unfold handoff_table_slot.
  apply pointer_location_value; eapply binary_expression_value.
  - apply handoff_array_value; exact LOCAL.
  - apply old_expression_value; apply value_int.
  - apply handoff_prefix_pointer_add; [reflexivity|lia|lia].
Qed.

Lemma handoff_table_assignment_edge e le before after output index rhs value :
  e ! EntrySource._args = Some (output,tarray (tptr tschar) 74) -> 0 <= index <= 73 ->
  expression_value handoff_ge e le before rhs value ->
  sem_cast value (typeof rhs) (tptr tschar) before = Some value ->
  Mem.store Mptr before output (8 * index) value = Some after ->
  forall k, store_edge handoff_ge
    (State EntrySource.f_guest (Sassign (handoff_table_slot index) rhs) k e le before)
    (State EntrySource.f_guest Sskip k e le after).
Proof.
  intros LOCAL BOUND VALUE CAST STORE k.
  eapply assignment_source_edge with (b:=output) (ofs:=Ptrofs.repr (8 * index)) (v:=value) (w:=value).
  - apply handoff_table_slot_location; assumption.
  - exact VALUE.
  - exact CAST.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    destruct (zle _ _) as [LIMIT|OVER]; [exact STORE|].
    exfalso; change (8 * index + 8 > 18446744073709551616) in OVER; lia.
Qed.

Lemma handoff_prefix_global_binding id : In id handoff_global_names ->
  Genv.find_symbol handoff_ge id = Some (handoff_symbol id).
Proof.
  unfold handoff_global_names; cbn; intros IN.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction; subst; reflexivity.
Qed.

Lemma handoff_prefix_global_array e le m id size :
  e ! id = None -> In id handoff_global_names ->
  expression_value handoff_ge e le m (Evar id (tarray tschar size))
    (Vptr (handoff_symbol id) Ptrofs.zero).
Proof.
  intros GLOBAL REGISTERED; eapply location_read_value.
  - apply global_location_value; [exact GLOBAL|apply handoff_prefix_global_binding; exact REGISTERED].
  - apply deref_loc_reference; reflexivity.
Qed.

Lemma handoff_prefix_global_scalar e le m id ty chunk value :
  e ! id = None -> In id handoff_global_names -> access_mode ty = By_value chunk ->
  Mem.loadv chunk m (Vptr (handoff_symbol id) Ptrofs.zero) = Some value ->
  expression_value handoff_ge e le m (Evar id ty) value.
Proof.
  intros GLOBAL REGISTERED TYPE LOAD; eapply location_read_value.
  - apply global_location_value; [exact GLOBAL|apply handoff_prefix_global_binding; exact REGISTERED].
  - eapply deref_loc_value; [exact TYPE|exact LOAD].
Qed.

Definition handoff_worker_mode preflight :=
  if Int.eq preflight Int.zero then EntrySource.___stringlit_112 else EntrySource.___stringlit_113.

Definition handoff_prefix_values b preflight mode offset :=
  [Vptr (handoff_symbol EntrySource.___stringlit_111) Ptrofs.zero;
   Vptr (handoff_symbol (handoff_worker_mode preflight)) Ptrofs.zero;
   Vptr (handoff_uid b) Ptrofs.zero;
   Vptr (handoff_symbol EntrySource._root_path) Ptrofs.zero;
   Vptr (handoff_numbers b) (Ptrofs.repr 0);
   Vptr (handoff_numbers b) (Ptrofs.repr 32);
   Vptr (handoff_numbers b) (Ptrofs.repr 64);
   Vptr (handoff_numbers b) (Ptrofs.repr 96);
   Vptr mode offset].

Lemma handoff_prefix_phase13_actual : guest_phase 13 =
  Sassign (handoff_table_slot 2) (Evar EntrySource._uid (tarray tschar 32)).
Proof. reflexivity. Qed.
Lemma handoff_prefix_phase14_actual : guest_phase 14 =
  Sassign (handoff_table_slot 3) (Evar EntrySource._root_path (tarray tschar 160)).
Proof. reflexivity. Qed.

Lemma handoff_prefix_phase11_edge b le before after k :
  Mem.store Mptr before (handoff_arguments b) 0
    (Vptr (handoff_symbol EntrySource.___stringlit_111) Ptrofs.zero) = Some after ->
  store_edge handoff_ge
    (State EntrySource.f_guest (guest_phase 11) k (handoff_locals_env b) le before)
    (State EntrySource.f_guest Sskip k (handoff_locals_env b) le after).
Proof.
  intros STORE; rewrite guest_argument_start_actual.
  change (store_edge handoff_ge
    (State EntrySource.f_guest
      (Sassign (handoff_table_slot 0) (Evar EntrySource.___stringlit_111 (tarray tschar 16)))
      k (handoff_locals_env b) le before)
    (State EntrySource.f_guest Sskip k (handoff_locals_env b) le after)).
  eapply handoff_table_assignment_edge.
  - unfold handoff_locals_env; WriteAll.lookup.
  - lia.
  - apply handoff_prefix_global_array.
    + apply handoff_nonlocal_binding; cbn; intuition discriminate.
    + unfold handoff_global_names; cbn; intuition congruence.
  - reflexivity.
  - exact STORE.
Qed.

Lemma handoff_prefix_phase13_edge b le before after k :
  Mem.store Mptr before (handoff_arguments b) 16 (Vptr (handoff_uid b) Ptrofs.zero) = Some after ->
  store_edge handoff_ge
    (State EntrySource.f_guest (guest_phase 13) k (handoff_locals_env b) le before)
    (State EntrySource.f_guest Sskip k (handoff_locals_env b) le after).
Proof.
  intros STORE; rewrite handoff_prefix_phase13_actual; eapply handoff_table_assignment_edge.
  - unfold handoff_locals_env; WriteAll.lookup.
  - lia.
  - apply handoff_array_value; unfold handoff_locals_env; WriteAll.lookup.
  - reflexivity.
  - exact STORE.
Qed.

Lemma handoff_prefix_phase14_edge b le before after k :
  Mem.store Mptr before (handoff_arguments b) 24
    (Vptr (handoff_symbol EntrySource._root_path) Ptrofs.zero) = Some after ->
  store_edge handoff_ge
    (State EntrySource.f_guest (guest_phase 14) k (handoff_locals_env b) le before)
    (State EntrySource.f_guest Sskip k (handoff_locals_env b) le after).
Proof.
  intros STORE; rewrite handoff_prefix_phase14_actual; eapply handoff_table_assignment_edge.
  - unfold handoff_locals_env; WriteAll.lookup.
  - lia.
  - apply handoff_prefix_global_array.
    + apply handoff_nonlocal_binding; cbn; intuition discriminate.
    + unfold handoff_global_names; cbn; intuition congruence.
  - reflexivity.
  - exact STORE.
Qed.

Definition handoff_mode_env le preflight :=
  PTree.set EntrySource._t'19 (Vptr (handoff_symbol (handoff_worker_mode preflight)) Ptrofs.zero)
    (PTree.set EntrySource._t'30 (Vint preflight) le).

Lemma handoff_prefix_phase12_actual : guest_phase 12 =
  Ssequence
    (Ssequence
      (Sset EntrySource._t'30 (Evar EntrySource._preflight tint))
      (Sifthenelse (Etempvar EntrySource._t'30 tint)
        (Sset EntrySource._t'19
          (Ecast (Evar EntrySource.___stringlit_113 (tarray tschar 6)) (tptr tschar)))
        (Sset EntrySource._t'19
          (Ecast (Evar EntrySource.___stringlit_112 (tarray tschar 4)) (tptr tschar)))))
    (Sassign (handoff_table_slot 1) (Etempvar EntrySource._t'19 (tptr tschar))).
Proof. reflexivity. Qed.

Lemma handoff_prefix_phase12_source b le before after preflight k :
  Mem.loadv Mint32 before (Vptr (handoff_symbol EntrySource._preflight) Ptrofs.zero) = Some (Vint preflight) ->
  Mem.store Mptr before (handoff_arguments b) 8
    (Vptr (handoff_symbol (handoff_worker_mode preflight)) Ptrofs.zero) = Some after ->
  store_path handoff_ge (fun current => current = before \/ current = after)
    (State EntrySource.f_guest (guest_phase 12) k (handoff_locals_env b) le before) 8
    (State EntrySource.f_guest Sskip k (handoff_locals_env b) (handoff_mode_env le preflight) after).
Proof.
  intros LOAD STORE; rewrite handoff_prefix_phase12_actual.
  eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [left; reflexivity|apply certified_set_edge|].
  - eapply handoff_prefix_global_scalar; [| |reflexivity|exact LOAD].
    + apply handoff_nonlocal_binding; cbn; intuition discriminate.
    + unfold handoff_global_names; cbn; intuition congruence.
  - eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
    unfold handoff_mode_env, handoff_worker_mode in STORE |- *.
    destruct (Int.eq preflight Int.zero) eqn:ZERO.
    + eapply store_next; [left; reflexivity|apply certified_if_edge with (v:=Vint preflight) (b:=false)|].
      * apply old_expression_value; apply value_temp; apply PTree.gss.
      * change (Some (negb (Int.eq preflight Int.zero)) = Some false); rewrite ZERO; reflexivity.
      * eapply store_next; [left; reflexivity|apply certified_set_edge|].
        -- eapply cast_expression_value.
           ++ apply handoff_prefix_global_array.
              ** apply handoff_nonlocal_binding; cbn; intuition discriminate.
              ** unfold handoff_global_names; cbn; intuition congruence.
           ++ reflexivity.
        -- eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
           eapply store_next; [left; reflexivity| |].
           ++ eapply handoff_table_assignment_edge with (value:=Vptr (handoff_symbol EntrySource.___stringlit_112) Ptrofs.zero);
                [unfold handoff_locals_env; WriteAll.lookup|lia| |reflexivity|exact STORE].
              apply old_expression_value; apply value_temp; apply PTree.gss.
           ++ apply store_done; right; reflexivity.
    + eapply store_next; [left; reflexivity|apply certified_if_edge with (v:=Vint preflight) (b:=true)|].
      * apply old_expression_value; apply value_temp; apply PTree.gss.
      * change (Some (negb (Int.eq preflight Int.zero)) = Some true); rewrite ZERO; reflexivity.
      * eapply store_next; [left; reflexivity|apply certified_set_edge|].
        -- eapply cast_expression_value.
           ++ apply handoff_prefix_global_array.
              ** apply handoff_nonlocal_binding; cbn; intuition discriminate.
              ** unfold handoff_global_names; cbn; intuition congruence.
           ++ reflexivity.
        -- eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
           eapply store_next; [left; reflexivity| |].
           ++ eapply handoff_table_assignment_edge with (value:=Vptr (handoff_symbol EntrySource.___stringlit_113) Ptrofs.zero);
                [unfold handoff_locals_env; WriteAll.lookup|lia| |reflexivity|exact STORE].
              apply old_expression_value; apply value_temp; apply PTree.gss.
           ++ apply store_done; right; reflexivity.
Qed.

Definition handoff_mode_pointer_env le mode offset :=
  PTree.set EntrySource._t'29 (Vptr mode offset) le.

Lemma handoff_prefix_phase16_actual : guest_phase 16 =
  Ssequence (Sset EntrySource._t'29 (Evar EntrySource._mode (tptr tschar)))
    (Sassign (handoff_table_slot 8)
      (Ecast (Etempvar EntrySource._t'29 (tptr tschar)) (tptr tschar))).
Proof. reflexivity. Qed.

Lemma handoff_prefix_phase16_source b le before after mode offset k :
  Mem.loadv Mptr before (Vptr (handoff_symbol EntrySource._mode) Ptrofs.zero) = Some (Vptr mode offset) ->
  Mem.store Mptr before (handoff_arguments b) 64 (Vptr mode offset) = Some after ->
  store_path handoff_ge (fun current => current = before \/ current = after)
    (State EntrySource.f_guest (guest_phase 16) k (handoff_locals_env b) le before) 4
    (State EntrySource.f_guest Sskip k (handoff_locals_env b) (handoff_mode_pointer_env le mode offset) after).
Proof.
  intros LOAD STORE; rewrite handoff_prefix_phase16_actual.
  eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [left; reflexivity|apply certified_set_edge|].
  - eapply handoff_prefix_global_scalar; [| |reflexivity|exact LOAD].
    + apply handoff_nonlocal_binding; cbn; intuition discriminate.
    + unfold handoff_global_names; cbn; intuition congruence.
  - eapply store_next; [left; reflexivity|apply unchanged_store_edge; WriteAll.structural|].
    eapply store_next; [left; reflexivity| |].
    + eapply handoff_table_assignment_edge with (value:=Vptr mode offset).
      * unfold handoff_locals_env; WriteAll.lookup.
      * lia.
      * eapply cast_expression_value.
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- reflexivity.
      * reflexivity.
      * exact STORE.
    + apply store_done; right; reflexivity.
Qed.

Lemma handoff_prefix_phase17_actual : guest_phase 17 =
  Sset EntrySource._i__2 (Ecast (Econst_int (Int.repr 0) tint) tulong).
Proof. reflexivity. Qed.

Lemma handoff_prefix_phase17_edge e le m k :
  store_edge handoff_ge (State EntrySource.f_guest (guest_phase 17) k e le m)
    (State EntrySource.f_guest Sskip k e (PTree.set EntrySource._i__2 (Vlong Int64.zero) le) m).
Proof.
  rewrite handoff_prefix_phase17_actual; apply certified_set_edge; eapply cast_expression_value.
  - apply old_expression_value; apply value_int.
  - reflexivity.
Qed.

Definition handoff_number_loop := match guest_phase 15 with Ssequence _ loop => loop | _ => Sskip end.
Definition handoff_number_body := match handoff_number_loop with Sloop body _ => body | _ => Sskip end.
Definition handoff_number_increment := match handoff_number_loop with Sloop _ increment => increment | _ => Sskip end.
Definition handoff_number_test := match handoff_number_body with Ssequence test _ => test | _ => Sskip end.
Definition handoff_number_store := match handoff_number_body with Ssequence _ store => store | _ => Sskip end.

Lemma handoff_number_phase_actual : guest_phase 15 =
  Ssequence (Sset EntrySource._i__1 (Econst_int (Int.repr 0) tint)) handoff_number_loop.
Proof. reflexivity. Qed.
Lemma handoff_number_loop_actual : handoff_number_loop = Sloop handoff_number_body handoff_number_increment.
Proof. reflexivity. Qed.
Lemma handoff_number_body_actual : handoff_number_body = Ssequence handoff_number_test handoff_number_store.
Proof. reflexivity. Qed.
Lemma handoff_number_test_actual : handoff_number_test =
  Sifthenelse (Ebinop Olt (Etempvar EntrySource._i__1 tuint) (Econst_int (Int.repr 4) tint) tint) Sskip Sbreak.
Proof. reflexivity. Qed.
Lemma handoff_number_increment_actual : handoff_number_increment =
  Sset EntrySource._i__1 (Ebinop Oadd (Etempvar EntrySource._i__1 tuint)
    (Econst_int (Int.repr 1) tint) tuint).
Proof. reflexivity. Qed.
Lemma handoff_number_store_actual : handoff_number_store =
  Sassign
    (Ederef (Ebinop Oadd (Evar EntrySource._args (tarray (tptr tschar) 74))
      (Ebinop Oadd (Econst_int (Int.repr 4) tint) (Etempvar EntrySource._i__1 tuint) tuint)
      (tptr (tptr tschar))) (tptr tschar))
    (Ederef (Ebinop Oadd (Evar EntrySource._numbers (tarray (tarray tschar 32) 4))
      (Etempvar EntrySource._i__1 tuint) (tptr (tarray tschar 32))) (tarray tschar 32)).
Proof. reflexivity. Qed.

Lemma handoff_number_test_operation ge m index : 0 <= index <= 4 ->
  sem_binary_operation ge Olt (Vint (Int.repr index)) tuint (Vint (Int.repr 4)) tint m =
  Some (Val.of_bool (index <? 4)).
Proof.
  intros INDEX.
  change (Some (Val.of_bool (Int.ltu (Int.repr index) (Int.repr 4))) =
    Some (Val.of_bool (index <? 4))).
  unfold Int.ltu; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  change (Some (Val.of_bool (if zlt index 4 then true else false)) = Some (Val.of_bool (index <? 4))).
  destruct (zlt index 4).
  - rewrite (proj2 (Z.ltb_lt index 4) ltac:(lia)); reflexivity.
  - rewrite (proj2 (Z.ltb_ge index 4) ltac:(lia)); reflexivity.
Qed.

Lemma handoff_number_increment_operation ge m index : 0 <= index <= 4 ->
  sem_binary_operation ge Oadd (Vint (Int.repr index)) tuint (Vint (Int.repr 1)) tint m =
  Some (Vint (Int.repr (index + 1))).
Proof.
  intros INDEX; change (Some (Vint (Int.add (Int.repr index) Int.one)) = Some (Vint (Int.repr (index + 1)))).
  unfold Int.add; change (Some (Vint (Int.repr (Int.unsigned (Int.repr index) + 1))) = Some (Vint (Int.repr (index + 1)))).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia); reflexivity.
Qed.

Lemma handoff_number_destination_operation ge m index : 0 <= index <= 4 ->
  sem_binary_operation ge Oadd (Vint (Int.repr 4)) tint (Vint (Int.repr index)) tuint m =
  Some (Vint (Int.repr (4 + index))).
Proof.
  intros INDEX; change (Some (Vint (Int.add (Int.repr 4) (Int.repr index))) = Some (Vint (Int.repr (4 + index)))).
  unfold Int.add; change (Some (Vint (Int.repr (4 + Int.unsigned (Int.repr index)))) = Some (Vint (Int.repr (4 + index)))).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia); reflexivity.
Qed.

Lemma handoff_number_store_edge b le before after index k :
  le ! EntrySource._i__1 = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  Mem.store Mptr before (handoff_arguments b) (8 * (4 + index))
    (Vptr (handoff_numbers b) (Ptrofs.repr (32 * index))) = Some after ->
  store_edge handoff_ge (State EntrySource.f_guest handoff_number_store k (handoff_locals_env b) le before)
    (State EntrySource.f_guest Sskip k (handoff_locals_env b) le after).
Proof.
  intros INDEX BOUND STORE; rewrite handoff_number_store_actual.
  eapply assignment_source_edge with (b:=handoff_arguments b) (ofs:=Ptrofs.repr (8 * (4 + index)))
    (v:=Vptr (handoff_numbers b) (Ptrofs.repr (32 * index)))
    (w:=Vptr (handoff_numbers b) (Ptrofs.repr (32 * index))).
  - apply pointer_location_value; eapply binary_expression_value.
    + apply handoff_array_value; unfold handoff_locals_env; WriteAll.lookup.
    + eapply binary_expression_value.
      * apply old_expression_value; apply value_int.
      * apply old_expression_value; apply value_temp; exact INDEX.
      * apply handoff_number_destination_operation; lia.
    + apply handoff_prefix_pointer_add; [reflexivity|lia|lia].
  - eapply location_read_value with (b:=handoff_numbers b) (ofs:=Ptrofs.repr (32 * index)).
    + apply pointer_location_value; eapply binary_expression_value.
      * apply handoff_array_value; unfold handoff_locals_env; WriteAll.lookup.
      * apply old_expression_value; apply value_temp; exact INDEX.
      * apply handoff_prefix_pointer_add; [reflexivity|lia|lia].
    + apply deref_loc_reference; reflexivity.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    destruct (zle _ _) as [LIMIT|OVER]; [exact STORE|].
    exfalso; change (8 * (4 + index) + 8 > 18446744073709551616) in OVER; lia.
Qed.

Fixpoint handoff_number_values numbers index count : list val :=
  match count with
  | O => []
  | S rest => Vptr numbers (Ptrofs.repr (32 * index)) :: handoff_number_values numbers (index + 1) rest
  end.

Lemma handoff_number_guard_edge b le m index k :
  le ! EntrySource._i__1 = Some (Vint (Int.repr index)) -> 0 <= index <= 4 ->
  store_edge handoff_ge
    (State EntrySource.f_guest handoff_number_test k (handoff_locals_env b) le m)
    (State EntrySource.f_guest (if index <? 4 then Sskip else Sbreak) k (handoff_locals_env b) le m).
Proof.
  intros INDEX BOUND; rewrite handoff_number_test_actual.
  apply certified_if_edge with (v:=Val.of_bool (index <? 4)).
  - eapply binary_expression_value.
    + apply old_expression_value; apply value_temp; exact INDEX.
    + apply old_expression_value; apply value_int.
    + apply handoff_number_test_operation; exact BOUND.
  - destruct (index <? 4); reflexivity.
Qed.

Lemma handoff_number_increment_edge b le m index k :
  le ! EntrySource._i__1 = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  store_edge handoff_ge
    (State EntrySource.f_guest handoff_number_increment k (handoff_locals_env b) le m)
    (State EntrySource.f_guest Sskip k (handoff_locals_env b)
      (PTree.set EntrySource._i__1 (Vint (Int.repr (index + 1))) le) m).
Proof.
  intros INDEX BOUND; rewrite handoff_number_increment_actual; apply certified_set_edge.
  eapply binary_expression_value.
  - apply old_expression_value; apply value_temp; exact INDEX.
  - apply old_expression_value; apply value_int.
  - apply handoff_number_increment_operation; lia.
Qed.

Theorem handoff_number_loop_source_bounded b base : forall remaining index before after le k,
  0 <= index -> index + Z.of_nat remaining = 4 ->
  le ! EntrySource._i__1 = Some (Vint (Int.repr index)) ->
  handoff_args_frame (handoff_arguments b) base before ->
  handoff_pointer_stores (handoff_arguments b) (4 + index) before
    (handoff_number_values (handoff_numbers b) index remaining) after ->
  exists count final,
    (count <= 8 * remaining + 5)%nat /\
    final ! EntrySource._i__1 = Some (Vint (Int.repr 4)) /\
    (forall id, id <> EntrySource._i__1 -> final ! id = le ! id) /\
    store_path handoff_ge (handoff_args_frame (handoff_arguments b) base)
      (State EntrySource.f_guest handoff_number_loop k (handoff_locals_env b) le before) count
      (State EntrySource.f_guest Sskip k (handoff_locals_env b) final after).
Proof.
  induction remaining as [|rest IH]; intros index before after le k LOW HIGH INDEX FRAME STORES.
  - cbn [Z.of_nat] in HIGH; assert (index=4) by lia; subst index.
    cbn [handoff_number_values handoff_pointer_stores handoff_pointer_cells] in STORES.
    inversion STORES; subst after.
    exists 5%nat,le; split; [lia|]. split; [exact INDEX|]. split; [auto|].
    rewrite handoff_number_loop_actual.
    eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
    rewrite handoff_number_body_actual.
    eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
    eapply store_next; [exact FRAME| |].
    + apply handoff_number_guard_edge; [exact INDEX|lia].
    + eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
      eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
      apply store_done; exact FRAME.
  - assert (BOUND : 0 <= index < 4) by (rewrite Nat2Z.inj_succ in HIGH; lia).
    cbn [handoff_number_values handoff_pointer_stores handoff_pointer_cells] in STORES.
    inversion STORES as [|? ? ? middle ? STORE TAIL]; subst.
    assert (MID : handoff_args_frame (handoff_arguments b) base middle)
      by (eapply handoff_args_store_frame; eassumption).
    set (advanced := PTree.set EntrySource._i__1 (Vint (Int.repr (index + 1))) le).
    destruct (IH (index + 1) middle after advanced k ltac:(lia)
      ltac:(rewrite Nat2Z.inj_succ in HIGH; lia) ltac:(unfold advanced; apply PTree.gss)
      MID ltac:(replace (4 + (index + 1)) with (4 + index + 1) by lia; exact TAIL))
      as [count [final [COUNTBOUND [FINALINDEX [OTHERS PATH]]]]].
    exists (8+count)%nat,final; split; [lia|]. split; [exact FINALINDEX|]. split.
    + intros id DIFFERENT; rewrite OTHERS by exact DIFFERENT.
      unfold advanced; rewrite PTree.gso by congruence; reflexivity.
    + eapply store_path_trans with (n:=8%nat) (b:=
        State EntrySource.f_guest handoff_number_loop k (handoff_locals_env b) advanced middle).
      * rewrite handoff_number_loop_actual at 1.
        eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
        rewrite handoff_number_body_actual at 1.
        eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
        eapply store_next; [exact FRAME| |].
        -- apply handoff_number_guard_edge; [exact INDEX|lia].
        -- rewrite (proj2 (Z.ltb_lt index 4) ltac:(lia)).
           eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
           eapply store_next; [exact FRAME|apply handoff_number_store_edge with (index:=index) (after:=middle); [exact INDEX|exact BOUND|exact STORE]|].
           eapply store_next; [exact MID|apply unchanged_store_edge; WriteAll.structural|].
           eapply store_next; [exact MID|apply handoff_number_increment_edge with (index:=index); [exact INDEX|exact BOUND]|].
           eapply store_next; [exact MID|apply unchanged_store_edge; WriteAll.structural|].
           apply store_done; exact MID.
      * exact PATH.
Qed.

Theorem handoff_number_loop_source b base : forall remaining index before after le k,
  0 <= index -> index + Z.of_nat remaining = 4 ->
  le ! EntrySource._i__1 = Some (Vint (Int.repr index)) ->
  handoff_args_frame (handoff_arguments b) base before ->
  handoff_pointer_stores (handoff_arguments b) (4 + index) before
    (handoff_number_values (handoff_numbers b) index remaining) after ->
  exists count final,
    final ! EntrySource._i__1 = Some (Vint (Int.repr 4)) /\
    (forall id, id <> EntrySource._i__1 -> final ! id = le ! id) /\
    store_path handoff_ge (handoff_args_frame (handoff_arguments b) base)
      (State EntrySource.f_guest handoff_number_loop k (handoff_locals_env b) le before) count
      (State EntrySource.f_guest Sskip k (handoff_locals_env b) final after).
Proof.
  intros remaining index before after le k LOW HIGH INDEX FRAME STORES.
  destruct(handoff_number_loop_source_bounded b base remaining index before after le k LOW HIGH INDEX FRAME STORES)
    as[count[final[BOUND REST]]]. exists count,final;exact REST.
Qed.

Theorem handoff_number_phase_source_bounded b base before after le k :
  handoff_args_frame (handoff_arguments b) base before ->
  handoff_pointer_stores (handoff_arguments b) 4 before
    (handoff_number_values (handoff_numbers b) 0 4) after ->
  exists count final,
    (count <= 40)%nat /\
    final ! EntrySource._i__1 = Some (Vint (Int.repr 4)) /\
    (forall id, id <> EntrySource._i__1 -> final ! id = le ! id) /\
    store_path handoff_ge (handoff_args_frame (handoff_arguments b) base)
      (State EntrySource.f_guest (guest_phase 15) k (handoff_locals_env b) le before) count
      (State EntrySource.f_guest Sskip k (handoff_locals_env b) final after).
Proof.
  intros FRAME STORES.
  set (initial := PTree.set EntrySource._i__1 (Vint Int.zero) le).
  destruct (handoff_number_loop_source_bounded b base 4 0 before after initial k
    ltac:(lia) eq_refl ltac:(unfold initial; apply PTree.gss) FRAME STORES)
    as [count [final [COUNTBOUND [INDEX [OTHERS PATH]]]]].
  exists (3+count)%nat,final; split; [lia|]. split; [exact INDEX|]. split.
  - intros id DIFFERENT; rewrite OTHERS by exact DIFFERENT; unfold initial;
      rewrite PTree.gso by congruence; reflexivity.
  - rewrite handoff_number_phase_actual; eapply store_path_trans with (n:=3%nat).
    + eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
      eapply store_next; [exact FRAME|apply certified_set_edge; apply old_expression_value; apply value_int|].
      eapply store_next; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
      apply store_done; exact FRAME.
    + exact PATH.
Qed.

Theorem handoff_number_phase_source b base before after le k :
  handoff_args_frame (handoff_arguments b) base before ->
  handoff_pointer_stores (handoff_arguments b) 4 before
    (handoff_number_values (handoff_numbers b) 0 4) after ->
  exists count final,
    final ! EntrySource._i__1 = Some (Vint (Int.repr 4)) /\
    (forall id, id <> EntrySource._i__1 -> final ! id = le ! id) /\
    store_path handoff_ge (handoff_args_frame (handoff_arguments b) base)
      (State EntrySource.f_guest (guest_phase 15) k (handoff_locals_env b) le before) count
      (State EntrySource.f_guest Sskip k (handoff_locals_env b) final after).
Proof.
  intros FRAME STORES.
  destruct(handoff_number_phase_source_bounded b base before after le k FRAME STORES)
    as[count[final[BOUND REST]]]. exists count,final;exact REST.
Qed.

Theorem handoff_argument_prefix_structure : guest_argument_tail =
  Ssequence (guest_phase 11)
    (Ssequence (guest_phase 12)
      (Ssequence (guest_phase 13)
        (Ssequence (guest_phase 14)
          (Ssequence (guest_phase 15)
            (Ssequence (guest_phase 16)
              (Ssequence (guest_phase 17)
                (Ssequence guest_copy_arguments (guest_tail 19 (fn_body EntrySource.f_guest))))))))).
Proof. reflexivity. Qed.

Theorem handoff_argument_prefix_source_bounded b before le preflight mode offset failure k :
  le ! EntrySource._failure = Some (Vint failure) ->
  Mem.range_perm before (handoff_arguments b) 0 592 Cur Freeable ->
  handoff_symbol EntrySource._preflight <> handoff_arguments b ->
  handoff_symbol EntrySource._mode <> handoff_arguments b ->
  Mem.loadv Mint32 before (Vptr (handoff_symbol EntrySource._preflight) Ptrofs.zero) = Some (Vint preflight) ->
  Mem.loadv Mptr before (Vptr (handoff_symbol EntrySource._mode) Ptrofs.zero) = Some (Vptr mode offset) ->
  exists after count final,
    (count <= 100)%nat /\
    handoff_pointer_stores (handoff_arguments b) 0 before (handoff_prefix_values b preflight mode offset) after /\
    handoff_args_frame (handoff_arguments b) before after /\
    final ! EntrySource._i__2 = Some (Vlong Int64.zero) /\
    final ! EntrySource._failure = Some (Vint failure) /\
    store_path handoff_ge (handoff_args_frame (handoff_arguments b) before)
      (State EntrySource.f_guest guest_argument_tail k (handoff_locals_env b) le before) count
      (State EntrySource.f_guest guest_copy_arguments (Kseq (guest_tail 19 (fn_body EntrySource.f_guest)) k)
        (handoff_locals_env b) final after).
Proof.
  intros FAILURE OWN PREFLIGHT_SEPARATE MODE_SEPARATE PREFLIGHT MODE.
  destruct (handoff_pointer_stores_exist (handoff_arguments b) 0 before
    (handoff_prefix_values b preflight mode offset) ltac:(lia) ltac:(cbn; lia) OWN) as [after STORES].
  pose proof STORES as CONTENTS.
  cbn [handoff_pointer_stores handoff_prefix_values handoff_pointer_cells] in STORES.
  inversion STORES as [|? ? ? m1 ? A0 T1]; subst.
  inversion T1 as [|? ? ? m2 ? A1 T2]; subst.
  inversion T2 as [|? ? ? m3 ? A2 T3]; subst.
  inversion T3 as [|? ? ? m4 ? A3 T4]; subst.
  inversion T4 as [|? ? ? m5 ? A4 T5]; subst.
  inversion T5 as [|? ? ? m6 ? A5 T6]; subst.
  inversion T6 as [|? ? ? m7 ? A6 T7]; subst.
  inversion T7 as [|? ? ? m8 ? A7 T8]; subst.
  inversion T8 as [|? ? ? m9 ? A8 T9]; subst.
  inversion T9; subst.
  assert (F0 : handoff_args_frame (handoff_arguments b) before before) by apply handoff_args_frame_refl.
  assert (F1 : handoff_args_frame (handoff_arguments b) before m1) by (eapply handoff_args_store_frame; eassumption).
  assert (F2 : handoff_args_frame (handoff_arguments b) before m2) by (eapply handoff_args_store_frame; eassumption).
  assert (F3 : handoff_args_frame (handoff_arguments b) before m3) by (eapply handoff_args_store_frame; eassumption).
  assert (F4 : handoff_args_frame (handoff_arguments b) before m4) by (eapply handoff_args_store_frame; eassumption).
  assert (F5 : handoff_args_frame (handoff_arguments b) before m5) by (eapply handoff_args_store_frame; eassumption).
  assert (F6 : handoff_args_frame (handoff_arguments b) before m6) by (eapply handoff_args_store_frame; eassumption).
  assert (F7 : handoff_args_frame (handoff_arguments b) before m7) by (eapply handoff_args_store_frame; eassumption).
  assert (F8 : handoff_args_frame (handoff_arguments b) before m8) by (eapply handoff_args_store_frame; eassumption).
  assert (F9 : handoff_args_frame (handoff_arguments b) before after) by
    (eapply handoff_args_store_frame; [exact F8|exact A8]).
  assert (PREFLIGHT1 : Mem.loadv Mint32 m1 (Vptr (handoff_symbol EntrySource._preflight) Ptrofs.zero) = Some (Vint preflight))
    by (eapply handoff_args_frame_loadv; eassumption).
  assert (MODE8 : Mem.loadv Mptr m8 (Vptr (handoff_symbol EntrySource._mode) Ptrofs.zero) = Some (Vptr mode offset))
    by (eapply handoff_args_frame_loadv; eassumption).
  assert (NUMBERS : handoff_pointer_stores (handoff_arguments b) 4 m4
    (handoff_number_values (handoff_numbers b) 0 4) m8).
  { cbn [handoff_pointer_stores handoff_number_values handoff_pointer_cells].
    econstructor; [exact A4|]. econstructor; [exact A5|]. econstructor; [exact A6|].
    econstructor; [exact A7|constructor]. }
  set (mode_env := handoff_mode_env le preflight).
  destruct (handoff_number_phase_source_bounded b before m4 m8 mode_env
    (Kseq (guest_tail 16 (fn_body EntrySource.f_guest)) k) F4 NUMBERS)
    as [number_count [number_env [NUMBER_BOUND [NUMBER_INDEX [NUMBER_OTHERS NUMBER_PATH]]]]].
  set (final := PTree.set EntrySource._i__2 (Vlong Int64.zero)
    (handoff_mode_pointer_env number_env mode offset)).
  exists after,(31+number_count)%nat,final; split; [lia|]. split; [exact CONTENTS|]. split; [exact F9|].
  split; [unfold final; apply PTree.gss|]. split.
  - unfold final,handoff_mode_pointer_env; rewrite !PTree.gso by discriminate.
    rewrite NUMBER_OTHERS by discriminate; unfold mode_env,handoff_mode_env; WriteAll.lookup.
  - rewrite handoff_argument_prefix_structure.
    eapply store_next; [exact F0|apply unchanged_store_edge; WriteAll.structural|].
    eapply store_next; [exact F0|apply handoff_prefix_phase11_edge; exact A0|].
    eapply store_next; [exact F1|apply unchanged_store_edge; WriteAll.structural|].
    eapply store_next; [exact F1|apply unchanged_store_edge; WriteAll.structural|].
    eapply store_path_trans with (n:=8%nat).
    + eapply number_path_implication with (P:=fun current => current=m1 \/ current=m2).
      * intros current [SAME|SAME]; subst; [exact F1|exact F2].
      * apply handoff_prefix_phase12_source; [exact PREFLIGHT1|exact A1].
    + eapply store_next; [exact F2|apply unchanged_store_edge; WriteAll.structural|].
      eapply store_next; [exact F2|apply unchanged_store_edge; WriteAll.structural|].
      eapply store_next; [exact F2|apply handoff_prefix_phase13_edge; exact A2|].
      eapply store_next; [exact F3|apply unchanged_store_edge; WriteAll.structural|].
      eapply store_next; [exact F3|apply unchanged_store_edge; WriteAll.structural|].
      eapply store_next; [exact F3|apply handoff_prefix_phase14_edge; exact A3|].
      eapply store_next; [exact F4|apply unchanged_store_edge; WriteAll.structural|].
      eapply store_next; [exact F4|apply unchanged_store_edge; WriteAll.structural|].
      match goal with|-store_path _ _ _ ?cost _=>replace cost with(number_count+11)%nat by lia end.
      eapply store_path_trans with (n:=number_count).
      * exact NUMBER_PATH.
      * eapply store_next; [exact F8|apply unchanged_store_edge; WriteAll.structural|].
        eapply store_next; [exact F8|apply unchanged_store_edge; WriteAll.structural|].
        eapply store_path_trans with (n:=4%nat).
        -- eapply number_path_implication with (P:=fun current => current=m8 \/ current=after).
           ++ intros current [SAME|SAME]; subst; [exact F8|exact F9].
           ++ apply handoff_prefix_phase16_source; [exact MODE8|exact A8].
        -- eapply store_next; [exact F9|apply unchanged_store_edge; WriteAll.structural|].
           eapply store_next; [exact F9|apply unchanged_store_edge; WriteAll.structural|].
           eapply store_next; [exact F9|apply handoff_prefix_phase17_edge|].
           eapply store_next; [exact F9|apply unchanged_store_edge; WriteAll.structural|].
           eapply store_next; [exact F9|apply unchanged_store_edge; WriteAll.structural|].
           apply store_done; exact F9.
Qed.

Theorem handoff_argument_prefix_source b before le preflight mode offset failure k :
  le ! EntrySource._failure = Some (Vint failure) ->
  Mem.range_perm before (handoff_arguments b) 0 592 Cur Freeable ->
  handoff_symbol EntrySource._preflight <> handoff_arguments b ->
  handoff_symbol EntrySource._mode <> handoff_arguments b ->
  Mem.loadv Mint32 before (Vptr (handoff_symbol EntrySource._preflight) Ptrofs.zero) = Some (Vint preflight) ->
  Mem.loadv Mptr before (Vptr (handoff_symbol EntrySource._mode) Ptrofs.zero) = Some (Vptr mode offset) ->
  exists after count final,
    handoff_pointer_stores (handoff_arguments b) 0 before (handoff_prefix_values b preflight mode offset) after /\
    handoff_args_frame (handoff_arguments b) before after /\
    final ! EntrySource._i__2 = Some (Vlong Int64.zero) /\
    final ! EntrySource._failure = Some (Vint failure) /\
    store_path handoff_ge (handoff_args_frame (handoff_arguments b) before)
      (State EntrySource.f_guest guest_argument_tail k (handoff_locals_env b) le before) count
      (State EntrySource.f_guest guest_copy_arguments (Kseq (guest_tail 19 (fn_body EntrySource.f_guest)) k)
        (handoff_locals_env b) final after).
Proof.
  intros FAILURE OWN PREFLIGHT_SEPARATE MODE_SEPARATE PREFLIGHT MODE.
  destruct(handoff_argument_prefix_source_bounded b before le preflight mode offset failure k
    FAILURE OWN PREFLIGHT_SEPARATE MODE_SEPARATE PREFLIGHT MODE)
    as[after[count[final[BOUND REST]]]]. exists after,count,final;exact REST.
Qed.
