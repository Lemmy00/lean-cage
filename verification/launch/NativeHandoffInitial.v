(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Real mode, handle initialization and UID guards before formatting. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ScalarMemory
  Library LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine HandoffRegion
  NativeHandoffStructure NativeHandoffArguments NativeHandoffAllocation NativeHandoffPrefix.
From LeanCageMainNumber Require Import NumberControl NumberInitial.
Import ListNotations.
Open Scope Z_scope.

Lemma handoff_strcmp_cases ge cell left right xs ys k m event target :
  c_string m left xs -> c_string m right ys ->
  entry_handoff_step ge cell
    (live (Callstate strcmp_definition [address_value left;address_value right] k m)) event target ->
  (exists value, strcmp_result m left right value /\
    event = entry_library (strcmp_returned left right value) /\
    target = live (Returnstate (Vint value) k m)) \/
  (event = entry_library library_wait /\
    target = live (Callstate strcmp_definition [address_value left;address_value right] k m)) \/
  (event = entry_library (original_event loss_step) /\ target = dead m).
Proof.
  intros LEFT RIGHT STEP; inversion STEP; subst; try discriminate.
  destruct (strcmp_boundary_cases _ _ _ _ _ _ _ _ _ _ LEFT RIGHT H)
    as [[value [RESULT [EVENT TARGET]]]|[[EVENT TARGET]|[EVENT TARGET]]]; subst; eauto.
Qed.

Definition handoff_handle_slot index :=
  Ederef (Ebinop Oadd (Evar EntrySource._handles (tarray tint 4))
    (Econst_int (Int.repr index) tint) (tptr tint)) tint.

Lemma handoff_handle_store_edge b le before after k index parameter value :
  0 <= index <= 3 -> le ! parameter = Some (Vint value) ->
  Mem.store Mint32 before (handoff_handles b) (4 * index) (Vint value) = Some after ->
  store_edge handoff_ge
    (State EntrySource.f_guest (Sassign (handoff_handle_slot index) (Etempvar parameter tint))
      k (handoff_locals_env b) le before)
    (State EntrySource.f_guest Sskip k (handoff_locals_env b) le after).
Proof.
  intros BOUND PARAMETER STORE; unfold handoff_handle_slot.
  eapply assignment_source_edge with (b:=handoff_handles b) (ofs:=Ptrofs.repr (4*index))
    (v:=Vint value) (w:=Vint value).
  - apply pointer_location_value; eapply binary_expression_value.
    + apply handoff_array_value; unfold handoff_locals_env; WriteAll.lookup.
    + apply old_expression_value; apply value_int.
    + apply handoff_prefix_pointer_add; [reflexivity|lia|lia].
  - apply old_expression_value; apply value_temp; exact PARAMETER.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    rewrite Ptrofs.unsigned_repr by
      (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    destruct (zle _ _) as [LIMIT|OVER]; [exact STORE|].
    exfalso; change (4*index+4>18446744073709551616) in OVER; lia.
Qed.

Definition handoff_handle_cells input output errors failure :=
  [{|scalar_chunk:=Mint32;scalar_offset:=0;scalar_value:=Vint input|};
   {|scalar_chunk:=Mint32;scalar_offset:=4;scalar_value:=Vint output|};
   {|scalar_chunk:=Mint32;scalar_offset:=8;scalar_value:=Vint errors|};
   {|scalar_chunk:=Mint32;scalar_offset:=12;scalar_value:=Vint failure|}].

Definition handoff_handle_stores b before input output errors failure after :=
  scalar_stores (handoff_handles b) before (handoff_handle_cells input output errors failure) after.

Lemma handoff_handle_stores_exist b before input output errors failure :
  Mem.range_perm before (handoff_handles b) 0 16 Cur Freeable ->
  exists after, handoff_handle_stores b before input output errors failure after.
Proof.
  intros OWN; unfold handoff_handle_stores.
  apply scalar_stores_exist with (size:=16); [|exact OWN].
  apply scalar_list_validb_sound; reflexivity.
Qed.

Lemma handoff_handle_store_frame handles base before after offset value :
  handoff_args_frame handles base before ->
  Mem.store Mint32 before handles offset (Vint value) = Some after ->
  handoff_args_frame handles base after.
Proof.
  intros FRAME STORE; eapply Mem.unchanged_on_trans; [exact FRAME|].
  eapply Mem.store_unchanged_on; [exact STORE|].
  intros position RANGE DIFFERENT; exact (DIFFERENT eq_refl).
Qed.

Theorem handoff_handle_initialization_source b before after le input output errors failure k :
  le ! EntrySource._input = Some (Vint input) ->
  le ! EntrySource._output = Some (Vint output) ->
  le ! EntrySource._errors = Some (Vint errors) ->
  le ! EntrySource._failure = Some (Vint failure) ->
  handoff_handle_stores b before input output errors failure after ->
  store_path handoff_ge (handoff_args_frame (handoff_handles b) before)
    (State EntrySource.f_guest (guest_tail 1 (fn_body EntrySource.f_guest))
      k (handoff_locals_env b) le before) 12
    (State EntrySource.f_guest (guest_tail 5 (fn_body EntrySource.f_guest))
      k (handoff_locals_env b) le after).
Proof.
  intros INPUT OUTPUT ERRORS FAILURE STORES.
  unfold handoff_handle_stores,handoff_handle_cells in STORES.
  inversion STORES as [|? ? ? m1 ? S0 T0]; subst.
  inversion T0 as [|? ? ? m2 ? S1 T1]; subst.
  inversion T1 as [|? ? ? m3 ? S2 T2]; subst.
  inversion T2 as [|? ? ? m4 ? S3 T3]; subst.
  inversion T3; subst.
  assert (F0:handoff_args_frame (handoff_handles b) before before) by apply handoff_args_frame_refl.
  assert (F1:handoff_args_frame (handoff_handles b) before m1)
    by (eapply handoff_handle_store_frame; [exact F0|exact S0]).
  assert (F2:handoff_args_frame (handoff_handles b) before m2)
    by (eapply handoff_handle_store_frame; [exact F1|exact S1]).
  assert (F3:handoff_args_frame (handoff_handles b) before m3)
    by (eapply handoff_handle_store_frame; [exact F2|exact S2]).
  assert (F4:handoff_args_frame (handoff_handles b) before after)
    by (eapply handoff_handle_store_frame; [exact F3|exact S3]).
  change (store_path handoff_ge (handoff_args_frame (handoff_handles b) before)
    (State EntrySource.f_guest
      (Ssequence (Sassign (handoff_handle_slot 0) (Etempvar EntrySource._input tint))
        (Ssequence (Sassign (handoff_handle_slot 1) (Etempvar EntrySource._output tint))
          (Ssequence (Sassign (handoff_handle_slot 2) (Etempvar EntrySource._errors tint))
            (Ssequence (Sassign (handoff_handle_slot 3) (Etempvar EntrySource._failure tint))
              (guest_tail 5 (fn_body EntrySource.f_guest))))))
      k (handoff_locals_env b) le before) 12
    (State EntrySource.f_guest (guest_tail 5 (fn_body EntrySource.f_guest))
      k (handoff_locals_env b) le after)).
  eapply store_next; [exact F0|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [exact F0|apply handoff_handle_store_edge with (value:=input); [lia|exact INPUT|exact S0]|].
  eapply store_next; [exact F1|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [exact F1|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [exact F1|apply handoff_handle_store_edge with (value:=output); [lia|exact OUTPUT|exact S1]|].
  eapply store_next; [exact F2|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [exact F2|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [exact F2|apply handoff_handle_store_edge with (value:=errors); [lia|exact ERRORS|exact S2]|].
  eapply store_next; [exact F3|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [exact F3|apply unchanged_store_edge; WriteAll.structural|].
  eapply store_next; [exact F3|apply handoff_handle_store_edge with (value:=failure); [lia|exact FAILURE|exact S3]|].
  eapply store_next; [exact F4|apply unchanged_store_edge; WriteAll.structural|].
  apply store_done; exact F4.
Qed.

Theorem handoff_handle_initialization_values b before after input output errors failure :
  handoff_handle_stores b before input output errors failure after ->
  Mem.load Mint32 after (handoff_handles b) 0 = Some (Vint input) /\
  Mem.load Mint32 after (handoff_handles b) 4 = Some (Vint output) /\
  Mem.load Mint32 after (handoff_handles b) 8 = Some (Vint errors) /\
  Mem.load Mint32 after (handoff_handles b) 12 = Some (Vint failure).
Proof.
  intros STORES; unfold handoff_handle_stores in STORES.
  pose proof (scalar_stores_fields _ _ _ _ STORES
    (scalar_orderedb_sound (handoff_handle_cells input output errors failure) eq_refl)) as LOAD.
  repeat split.
  - exact (LOAD {|scalar_chunk:=Mint32;scalar_offset:=0;scalar_value:=Vint input|}
      ltac:(unfold handoff_handle_cells; cbn; intuition congruence)).
  - exact (LOAD {|scalar_chunk:=Mint32;scalar_offset:=4;scalar_value:=Vint output|}
      ltac:(unfold handoff_handle_cells; cbn; intuition congruence)).
  - exact (LOAD {|scalar_chunk:=Mint32;scalar_offset:=8;scalar_value:=Vint errors|}
      ltac:(unfold handoff_handle_cells; cbn; intuition congruence)).
  - exact (LOAD {|scalar_chunk:=Mint32;scalar_offset:=12;scalar_value:=Vint failure|}
      ltac:(unfold handoff_handle_cells; cbn; intuition congruence)).
Qed.

Lemma handoff_strcmp_region ge cell P R left right xs ys k m remaining :
  P m -> c_string m left xs -> c_string m right ys ->
  (forall value, strcmp_result m left right value ->
    handoff_region ge cell P R remaining (Returnstate (Vint value) k m)) ->
  handoff_region ge cell P R (S remaining)
    (Callstate strcmp_definition [address_value left;address_value right] k m).
Proof.
  intros GOOD LEFT RIGHT RETURN; eapply handoff_region_next; [exact GOOD| |].
  - destruct (strcmp_progress m left right) as [value RESULT]; [exists xs,ys; auto|].
    exists (entry_library (strcmp_returned left right value)), (Returnstate (Vint value) k m).
    split; [reflexivity|]. split; [reflexivity|].
    apply entry_library_step, strcmp_step; exact RESULT.
  - intros event target STEP.
    destruct (handoff_strcmp_cases _ _ _ _ _ _ _ _ _ _ LEFT RIGHT STEP)
      as [[value [RESULT [EVENT TARGET]]]|[[EVENT TARGET]|[EVENT TARGET]]]; subst.
    + right; right; exists (Returnstate (Vint value) k m).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; exact RESULT].
    + left; auto.
    + right; left; exists m; auto.
Qed.

Definition handoff_initial_failure :=
  Scall None (Evar EntrySource._fail_child (Tfunction [tint;tuint;tint] tvoid cc_default))
    [Etempvar EntrySource._failure tint; Econst_int (Int.repr 1) tint;
     Econst_int (Int.repr 22) tint].

Definition handoff_mode_loaded le mode offset :=
  PTree.set EntrySource._t'43 (Vptr mode offset) le.

Definition handoff_mode_cont b le mode offset k :=
  Kcall (Some EntrySource._t'1) EntrySource.f_guest (handoff_locals_env b)
    (handoff_mode_loaded le mode offset)
    (Kseq (Sifthenelse (Etempvar EntrySource._t'1 tint) handoff_initial_failure Sskip)
      (Kseq (guest_tail 1 (fn_body EntrySource.f_guest)) k)).

Lemma handoff_mode_body_actual : fn_body EntrySource.f_guest =
  Ssequence
    (Ssequence
      (Ssequence (Sset EntrySource._t'43 (Evar EntrySource._mode (tptr tschar)))
        (Scall (Some EntrySource._t'1)
          (Evar EntrySource._strcmp (Tfunction [tptr tschar;tptr tschar] tint cc_default))
          [Etempvar EntrySource._t'43 (tptr tschar);
           Evar EntrySource.___stringlit_1 (tarray tschar 7)]))
      (Sifthenelse (Etempvar EntrySource._t'1 tint) handoff_initial_failure Sskip))
    (guest_tail 1 (fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.

Lemma handoff_strcmp_binding :
  Genv.find_symbol handoff_ge EntrySource._strcmp = Some (handoff_symbol EntrySource._strcmp) /\
  Genv.find_funct handoff_ge (Vptr (handoff_symbol EntrySource._strcmp) Ptrofs.zero) =
    Some strcmp_definition.
Proof. split; reflexivity. Qed.

Lemma handoff_fail_child_binding :
  Genv.find_symbol handoff_ge EntrySource._fail_child = Some (handoff_symbol EntrySource._fail_child) /\
  Genv.find_funct handoff_ge (Vptr (handoff_symbol EntrySource._fail_child) Ptrofs.zero) =
    Some (Internal EntrySource.f_fail_child).
Proof. split; reflexivity. Qed.

Theorem handoff_mode_source b le m mode offset k :
  Mem.loadv Mptr m (Vptr (handoff_symbol EntrySource._mode) Ptrofs.zero) = Some (Vptr mode offset) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest (fn_body EntrySource.f_guest) k (handoff_locals_env b) le m) 6
    (Callstate strcmp_definition
      [Vptr mode offset; Vptr (handoff_symbol EntrySource.___stringlit_1) Ptrofs.zero]
      (handoff_mode_cont b le mode offset k) m).
Proof.
  intros MODE; rewrite handoff_mode_body_actual at 1; unfold handoff_mode_cont.
  handoff_route; handoff_route; handoff_route; handoff_set.
  - apply handoff_prefix_global_scalar with (chunk:=Mptr).
    + apply handoff_nonlocal_binding; cbn; intuition discriminate.
    + unfold handoff_global_names; cbn; intuition congruence.
    + reflexivity.
    + exact MODE.
  - handoff_route; eapply store_next; [reflexivity| |].
    + eapply certified_call_edge.
      * reflexivity.
      * apply old_expression_value; eapply value_function.
        -- apply handoff_nonlocal_binding; cbn; intuition discriminate.
        -- exact (proj1 handoff_strcmp_binding).
        -- reflexivity.
      * eapply cons_argument_values.
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- reflexivity.
        -- eapply cons_argument_values.
           ++ apply handoff_prefix_global_array.
              ** apply handoff_nonlocal_binding; cbn; intuition discriminate.
              ** unfold handoff_global_names; cbn; intuition congruence.
           ++ reflexivity.
           ++ apply no_argument_values.
      * exact (proj2 handoff_strcmp_binding).
      * reflexivity.
    + apply store_done; reflexivity.
Qed.

Definition handoff_mode_returned le mode offset value :=
  PTree.set EntrySource._t'1 (Vint value) (handoff_mode_loaded le mode offset).

Theorem handoff_mode_return_source b le m mode offset k value :
  store_path handoff_ge (fun after => after = m)
    (Returnstate (Vint value) (handoff_mode_cont b le mode offset k) m) 3
    (State EntrySource.f_guest
      (if Int.eq value Int.zero then Sskip else handoff_initial_failure)
      (Kseq (guest_tail 1 (fn_body EntrySource.f_guest)) k)
      (handoff_locals_env b) (handoff_mode_returned le mode offset value) m).
Proof.
  unfold handoff_mode_cont, handoff_mode_returned.
  replace (if Int.eq value Int.zero then Sskip else handoff_initial_failure)
    with (if negb (Int.eq value Int.zero) then handoff_initial_failure else Sskip)
    by (destruct (Int.eq value Int.zero); reflexivity).
  handoff_route; handoff_route.
  eapply store_next; [reflexivity| |].
  - eapply certified_if_edge with (v:=Vint value) (b:=negb (Int.eq value Int.zero)).
    + apply old_expression_value; apply value_temp; apply PTree.gss.
    + reflexivity.
  - apply store_done; reflexivity.
Qed.

Theorem handoff_initial_failure_call b le m failure k :
  le ! EntrySource._failure = Some (Vint failure) ->
  store_edge handoff_ge
    (State EntrySource.f_guest handoff_initial_failure k (handoff_locals_env b) le m)
    (Callstate (Internal EntrySource.f_fail_child)
      [Vint failure;Vint Int.one;Vint (Int.repr 22)]
      (Kcall None EntrySource.f_guest (handoff_locals_env b) le k) m).
Proof.
  intros FAILURE; unfold handoff_initial_failure; eapply certified_call_edge.
  - reflexivity.
  - apply old_expression_value; eapply value_function.
    + apply handoff_nonlocal_binding; cbn; intuition discriminate.
    + exact (proj1 handoff_fail_child_binding).
    + reflexivity.
  - eapply cons_argument_values.
    + apply old_expression_value; apply value_temp; exact FAILURE.
    + reflexivity.
    + eapply cons_argument_values.
      * apply old_expression_value; apply value_int.
      * reflexivity.
      * eapply cons_argument_values.
        -- apply old_expression_value; apply value_int.
        -- reflexivity.
        -- apply no_argument_values.
  - exact (proj2 handoff_fail_child_binding).
  - reflexivity.
Qed.

Definition handoff_uid_low uid := Int.unsigned uid <? 100000.
Definition handoff_uid_high uid := 100999 <? Int.unsigned uid.
Definition handoff_uid_bad uid := handoff_uid_low uid || handoff_uid_high uid.

Definition handoff_uid_choose :=
  Ssequence (Sset EntrySource._t'41 (Evar EntrySource._run_uid tuint))
    (Sifthenelse (Ebinop Olt (Etempvar EntrySource._t'41 tuint)
        (Econst_int (Int.repr 100000) tint) tint)
      (Sset EntrySource._t'2 (Econst_int (Int.repr 1) tint))
      (Ssequence (Sset EntrySource._t'42 (Evar EntrySource._run_uid tuint))
        (Sset EntrySource._t'2 (Ecast
          (Ebinop Ogt (Etempvar EntrySource._t'42 tuint)
            (Econst_int (Int.repr 100999) tint) tint) tbool)))).

Definition handoff_uid_env le uid :=
  if handoff_uid_low uid then
    PTree.set EntrySource._t'2 (Vint Int.one) (PTree.set EntrySource._t'41 (Vint uid) le)
  else PTree.set EntrySource._t'2 (Val.of_bool (handoff_uid_high uid))
    (PTree.set EntrySource._t'42 (Vint uid) (PTree.set EntrySource._t'41 (Vint uid) le)).

Lemma handoff_uid_phase_actual : guest_phase 5 =
  Ssequence handoff_uid_choose
    (Sifthenelse (Etempvar EntrySource._t'2 tint) handoff_initial_failure Sskip).
Proof. reflexivity. Qed.

Lemma handoff_uid_lower_value ge m uid :
  sem_binary_operation ge Olt (Vint uid) tuint (Vint (Int.repr 100000)) tint m =
    Some (Val.of_bool (handoff_uid_low uid)).
Proof.
  unfold handoff_uid_low; change
    (Some (Val.of_bool (Int.ltu uid (Int.repr 100000))) =
    Some (Val.of_bool (Int.unsigned uid <? 100000))).
  unfold Int.ltu; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  destruct (zlt (Int.unsigned uid) 100000).
  - rewrite (proj2 (Z.ltb_lt _ _) l); reflexivity.
  - rewrite (proj2 (Z.ltb_ge (Int.unsigned uid) 100000) ltac:(lia)); reflexivity.
Qed.

Lemma handoff_uid_upper_value ge m uid :
  sem_binary_operation ge Ogt (Vint uid) tuint (Vint (Int.repr 100999)) tint m =
    Some (Val.of_bool (handoff_uid_high uid)).
Proof.
  unfold handoff_uid_high; change
    (Some (Val.of_bool (Int.ltu (Int.repr 100999) uid)) =
    Some (Val.of_bool (100999 <? Int.unsigned uid))).
  unfold Int.ltu; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  destruct (zlt 100999 (Int.unsigned uid)).
  - rewrite (proj2 (Z.ltb_lt _ _) l); reflexivity.
  - rewrite (proj2 (Z.ltb_ge 100999 (Int.unsigned uid)) ltac:(lia)); reflexivity.
Qed.

Theorem handoff_uid_guard_source b le m uid k :
  Mem.loadv Mint32 m (Vptr (handoff_symbol EntrySource._run_uid) Ptrofs.zero) = Some (Vint uid) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest (guest_phase 5) k (handoff_locals_env b) le m)
    (if handoff_uid_low uid then 8%nat else 11%nat)
    (State EntrySource.f_guest (if handoff_uid_bad uid then handoff_initial_failure else Sskip)
      k (handoff_locals_env b) (handoff_uid_env le uid) m).
Proof.
  intros UID; rewrite handoff_uid_phase_actual; unfold handoff_uid_choose.
  destruct (handoff_uid_low uid) eqn:LOW.
  - unfold handoff_uid_env,handoff_uid_bad; rewrite LOW; cbn [orb].
    handoff_route; handoff_route; handoff_set.
    + apply handoff_prefix_global_scalar with (chunk:=Mint32).
      * apply handoff_nonlocal_binding; cbn; intuition discriminate.
      * unfold handoff_global_names; cbn; intuition congruence.
      * reflexivity.
      * exact UID.
    + handoff_route; eapply store_next; [reflexivity|apply certified_if_edge with (v:=Val.of_bool true) (b:=true)|].
      * eapply binary_expression_value.
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- apply old_expression_value; apply value_int.
        -- rewrite handoff_uid_lower_value,LOW; reflexivity.
      * reflexivity.
      * handoff_set; [apply old_expression_value; apply value_int|].
        handoff_route; eapply store_next; [reflexivity|apply certified_if_edge with (v:=Vint Int.one) (b:=true)|].
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- reflexivity.
        -- apply store_done; reflexivity.
  - unfold handoff_uid_env,handoff_uid_bad; rewrite LOW; cbn [orb].
    handoff_route; handoff_route; handoff_set.
    + apply handoff_prefix_global_scalar with (chunk:=Mint32).
      * apply handoff_nonlocal_binding; cbn; intuition discriminate.
      * unfold handoff_global_names; cbn; intuition congruence.
      * reflexivity.
      * exact UID.
    + handoff_route; eapply store_next; [reflexivity|apply certified_if_edge with (v:=Val.of_bool false) (b:=false)|].
      * eapply binary_expression_value.
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- apply old_expression_value; apply value_int.
        -- rewrite handoff_uid_lower_value,LOW; reflexivity.
      * reflexivity.
      * handoff_route; handoff_set.
        -- apply handoff_prefix_global_scalar with (chunk:=Mint32).
           ++ apply handoff_nonlocal_binding; cbn; intuition discriminate.
           ++ unfold handoff_global_names; cbn; intuition congruence.
           ++ reflexivity.
           ++ exact UID.
        -- handoff_route; handoff_set.
           ++ eapply cast_expression_value.
              ** eapply binary_expression_value.
                 --- apply old_expression_value; apply value_temp; apply PTree.gss.
                 --- apply old_expression_value; apply value_int.
                 --- apply handoff_uid_upper_value.
              ** apply number_bool_cast.
           ++ handoff_route; eapply store_next; [reflexivity|apply certified_if_edge with
                (v:=Val.of_bool (handoff_uid_high uid)) (b:=handoff_uid_high uid)|].
              ** apply old_expression_value; apply value_temp; apply PTree.gss.
              ** apply number_bool_value.
              ** apply store_done; reflexivity.
Qed.

Theorem handoff_uid_checked uid : handoff_uid_bad uid = false <->
  100000 <= Int.unsigned uid <= 100999.
Proof.
  unfold handoff_uid_bad,handoff_uid_low,handoff_uid_high.
  rewrite Bool.orb_false_iff, !Z.ltb_ge; lia.
Qed.

Theorem handoff_initial_temps_preserved original mode offset value uid id :
  ~In id [EntrySource._t'1;EntrySource._t'43;EntrySource._t'2;
    EntrySource._t'41;EntrySource._t'42] ->
  (handoff_uid_env (handoff_mode_returned original mode offset value) uid) ! id = original ! id.
Proof.
  intros UNCHANGED; unfold handoff_uid_env,handoff_mode_returned,handoff_mode_loaded.
  destruct (handoff_uid_low uid);
    repeat (rewrite PTree.gso by (cbn in UNCHANGED; intuition congruence)); reflexivity.
Qed.

Theorem handoff_handle_stores_permissions b before after input output errors failure :
  handoff_handle_stores b before input output errors failure after ->
  forall object offset kind permission,
    Mem.perm after object offset kind permission <-> Mem.perm before object offset kind permission.
Proof. intros STORES; eapply scalar_stores_permissions; exact STORES. Qed.

Lemma handoff_handle_stores_frame b before after input output errors failure :
  handoff_handle_stores b before input output errors failure after ->
  handoff_args_frame (handoff_handles b) before after.
Proof.
  intros STORES; unfold handoff_handle_stores in STORES; induction STORES.
  - apply handoff_args_frame_refl.
  - eapply Mem.unchanged_on_trans; [|exact IHSTORES].
    eapply Mem.store_unchanged_on; [exact H|].
    intros position RANGE DIFFERENT; exact (DIFFERENT eq_refl).
Qed.

Definition handoff_normal_bytes := map Byte.repr [110;111;114;109;97;108].
Definition handoff_normal_address :=
  {|address_block:=handoff_symbol EntrySource.___stringlit_1;address_offset:=0|}.

Definition handoff_initial_leaf b before original mode failure uid modebytes k state :=
  (exists after continuation,
    state = Callstate (Internal EntrySource.f_fail_child)
      [Vint failure;Vint Int.one;Vint (Int.repr 22)] continuation after /\
    handoff_args_frame (handoff_handles b) before after /\ is_call_cont continuation) \/
  (exists after value,
    state = State EntrySource.f_guest (guest_tail 6 (fn_body EntrySource.f_guest))
      k (handoff_locals_env b)
      (handoff_uid_env (handoff_mode_returned original (address_block mode)
        (Ptrofs.repr (address_offset mode)) value) uid) after /\
    handoff_handle_stores b before
      (match original ! EntrySource._input with Some (Vint v)=>v|_=>Int.zero end)
      (match original ! EntrySource._output with Some (Vint v)=>v|_=>Int.zero end)
      (match original ! EntrySource._errors with Some (Vint v)=>v|_=>Int.zero end) failure after /\
    modebytes = handoff_normal_bytes /\ Int.eq value Int.zero = true /\
    100000 <= Int.unsigned uid <= 100999).

(* Allocation ownership and prepared global strings are inputs.  Neither good
   descriptor values nor a checked UID nor the production selector is assumed. *)
Theorem handoff_initial_region b before original input output errors failure uid mode modebytes k cell :
  original ! EntrySource._input = Some (Vint input) ->
  original ! EntrySource._output = Some (Vint output) ->
  original ! EntrySource._errors = Some (Vint errors) ->
  original ! EntrySource._failure = Some (Vint failure) ->
  Mem.range_perm before (handoff_handles b) 0 16 Cur Freeable ->
  handoff_symbol EntrySource._run_uid <> handoff_handles b ->
  Mem.loadv Mint32 before (Vptr (handoff_symbol EntrySource._run_uid) Ptrofs.zero) = Some (Vint uid) ->
  Mem.loadv Mptr before (Vptr (handoff_symbol EntrySource._mode) Ptrofs.zero) = Some (address_value mode) ->
  c_string before mode modebytes -> c_string before handoff_normal_address handoff_normal_bytes ->
  handoff_region handoff_ge cell (handoff_args_frame (handoff_handles b) before)
    (handoff_initial_leaf b before original mode failure uid modebytes k) 64
    (State EntrySource.f_guest (fn_body EntrySource.f_guest) k (handoff_locals_env b) original before).
Proof.
  intros INPUT OUTPUT ERRORS FAILURE OWN UID_SEPARATE UID MODE MODE_TEXT NORMAL_TEXT.
  assert (F0:handoff_args_frame (handoff_handles b) before before) by apply handoff_args_frame_refl.
  set (loaded := handoff_mode_loaded original (address_block mode) (Ptrofs.repr (address_offset mode))).
  eapply handoff_region_store_path with (count:=6%nat) (remaining:=58%nat).
  - eapply number_path_implication with (P:=fun after=>after=before).
    + intros after SAME; subst; exact F0.
    + apply handoff_mode_source; exact MODE.
  - change (handoff_region handoff_ge cell (handoff_args_frame (handoff_handles b) before)
      (handoff_initial_leaf b before original mode failure uid modebytes k) 58
      (Callstate strcmp_definition [address_value mode;address_value handoff_normal_address]
        (handoff_mode_cont b original (address_block mode) (Ptrofs.repr (address_offset mode)) k) before)).
    eapply handoff_strcmp_region with (remaining:=57%nat); [exact F0|exact MODE_TEXT|exact NORMAL_TEXT|].
    intros value COMPARED.
    pose proof (handoff_mode_return_source b original before (address_block mode)
      (Ptrofs.repr (address_offset mode)) k value) as RETURN.
    set (returned := handoff_mode_returned original (address_block mode)
      (Ptrofs.repr (address_offset mode)) value).
    assert (RI:returned ! EntrySource._input = Some (Vint input))
      by (unfold returned,handoff_mode_returned,handoff_mode_loaded; rewrite !PTree.gso by discriminate; exact INPUT).
    assert (RO:returned ! EntrySource._output = Some (Vint output))
      by (unfold returned,handoff_mode_returned,handoff_mode_loaded; rewrite !PTree.gso by discriminate; exact OUTPUT).
    assert (RE:returned ! EntrySource._errors = Some (Vint errors))
      by (unfold returned,handoff_mode_returned,handoff_mode_loaded; rewrite !PTree.gso by discriminate; exact ERRORS).
    assert (RF:returned ! EntrySource._failure = Some (Vint failure))
      by (unfold returned,handoff_mode_returned,handoff_mode_loaded; rewrite !PTree.gso by discriminate; exact FAILURE).
    eapply handoff_region_store_path with (count:=3%nat) (remaining:=54%nat).
    + eapply number_path_implication with (P:=fun after=>after=before).
      * intros after SAME; subst; exact F0.
      * exact RETURN.
    + destruct (Int.eq value Int.zero) eqn:ZERO.
      * assert (MODE_NORMAL:modebytes=handoff_normal_bytes)
          by (apply (proj1 (strcmp_zero_iff _ _ _ _ _ _ MODE_TEXT NORMAL_TEXT COMPARED)); exact ZERO).
        eapply handoff_region_source_prepend; [exact F0|apply unchanged_store_edge; WriteAll.structural|].
        destruct (handoff_handle_stores_exist b before input output errors failure OWN) as [after STORES].
        pose proof (handoff_handle_stores_frame _ _ _ _ _ _ _ STORES) as FRAME.
        eapply handoff_region_store_path with (count:=12%nat) (remaining:=41%nat).
        -- apply handoff_handle_initialization_source with
             (input:=input) (output:=output) (errors:=errors) (failure:=failure).
           ++ exact RI.
           ++ exact RO.
           ++ exact RE.
           ++ exact RF.
           ++ exact STORES.
        -- assert (UID_AFTER:Mem.loadv Mint32 after
             (Vptr (handoff_symbol EntrySource._run_uid) Ptrofs.zero)=Some(Vint uid))
             by (eapply handoff_args_frame_loadv; eassumption).
           change (handoff_region handoff_ge cell (handoff_args_frame (handoff_handles b) before)
             (handoff_initial_leaf b before original mode failure uid modebytes k) 41
             (State EntrySource.f_guest
               (Ssequence (guest_phase 5) (guest_tail 6 (fn_body EntrySource.f_guest)))
               k (handoff_locals_env b) returned after)).
           eapply handoff_region_source_prepend; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
           pose proof (handoff_uid_guard_source b returned after uid
             (Kseq (guest_tail 6 (fn_body EntrySource.f_guest)) k) UID_AFTER) as GUARDED.
           eapply handoff_region_weaken with (n:=
             ((if handoff_uid_low uid then 8%nat else 11%nat)+1)%nat).
           ++ eapply handoff_region_store_path with (remaining:=1%nat).
              ** eapply number_path_implication with (P:=fun current=>current=after).
                 --- intros current SAME; subst; exact FRAME.
                 --- exact GUARDED.
              ** destruct (handoff_uid_bad uid) eqn:BAD.
                 --- eapply handoff_region_source_prepend; [exact FRAME|apply handoff_initial_failure_call|].
                     +++ unfold handoff_uid_env; destruct (handoff_uid_low uid);
                           rewrite !PTree.gso by discriminate; exact RF.
                     +++ apply handoff_region_stop; [exact FRAME|].
                         left; eexists; eexists; split; [reflexivity|]. split; [exact FRAME|exact I].
                 --- eapply handoff_region_source_prepend; [exact FRAME|apply unchanged_store_edge; WriteAll.structural|].
                     apply handoff_region_stop; [exact FRAME|].
                     right; exists after,value; split; [reflexivity|].
                     split; [rewrite INPUT,OUTPUT,ERRORS; exact STORES|].
                     split; [exact MODE_NORMAL|]. split; [exact ZERO|].
                     apply (proj1 (handoff_uid_checked uid)); exact BAD.
           ++ destruct (handoff_uid_low uid); cbn; lia.
      * eapply handoff_region_weaken with (n:=1%nat); [|lia].
        eapply handoff_region_source_prepend; [exact F0|apply handoff_initial_failure_call; exact RF|].
        apply handoff_region_stop; [exact F0|].
        left; eexists; eexists; split; [reflexivity|]. split; [exact F0|exact I].
Qed.
