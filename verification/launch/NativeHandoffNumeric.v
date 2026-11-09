(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Source readback compares the actual produced bytes before handoff. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffStructure NativeHandoffArguments NativeHandoffPaths
  NativeHandoffNumberBound.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberControl NumberInitial NumberSource.
Import ListNotations.
Open Scope Z_scope.

Definition handoff_numeric_failure :=
  Scall None (Evar EntrySource._fail_child (Tfunction [tint;tuint;tint] tvoid cc_default))
    [Etempvar EntrySource._failure tint; Econst_int (Int.repr 1) tint; Econst_int (Int.repr 71) tint].

Definition handoff_numeric_choose code bad loaded getter getter_expression wanted_expression :=
  Sifthenelse (Etempvar code tint)
    (Sset bad (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sset loaded (Evar EntrySource._encoded tulong))
      (Ssequence
        (Sset getter getter_expression)
        (Sset bad (Ecast (Ebinop One (Etempvar loaded tulong) wanted_expression tint) tbool)))).

Definition handoff_numeric_reject bad :=
  Sifthenelse (Etempvar bad tint) handoff_numeric_failure Sskip.

Definition handoff_numeric_cont code bad loaded getter getter_expression wanted_expression e le k :=
  Kcall (Some code) EntrySource.f_guest e le
    (Kseq (handoff_numeric_choose code bad loaded getter getter_expression wanted_expression)
      (Kseq (handoff_numeric_reject bad) k)).

Definition handoff_numeric_bad parsed wanted :=
  match parsed with None => true | Some value => negb (value =? wanted) end.

Definition handoff_numeric_env code bad loaded getter le parsed wanted getter_value :=
  let returned := PTree.set code (number_code parsed) le in
  match parsed with
  | None => PTree.set bad (Vint Int.one) returned
  | Some value => PTree.set bad (Val.of_bool (negb (value =? wanted)))
      (PTree.set getter getter_value (PTree.set loaded (Vlong (Int64.repr value)) returned))
  end.

Theorem handoff_numeric_return_source e le m k code bad loaded getter
    getter_expression wanted_expression encoded parsed wanted getter_value comparison_value :
  getter <> loaded ->
  e ! EntrySource._encoded = Some (encoded,tulong) ->
  (forall value, parsed = Some value ->
    Mem.loadv Mint64 m (Vptr encoded Ptrofs.zero) = Some (Vlong (Int64.repr value))) ->
  (forall value, parsed = Some value ->
    expression_value handoff_ge e
      (PTree.set loaded (Vlong (Int64.repr value)) (PTree.set code (number_code parsed) le)) m
      getter_expression getter_value) ->
  (forall value, parsed = Some value ->
    expression_value handoff_ge e
      (PTree.set getter getter_value
        (PTree.set loaded (Vlong (Int64.repr value)) (PTree.set code (number_code parsed) le))) m
      wanted_expression comparison_value) ->
  (forall value, parsed = Some value ->
    sem_binary_operation handoff_ge One (Vlong (Int64.repr value)) tulong
      comparison_value (typeof wanted_expression) m = Some (Val.of_bool (negb (value =? wanted)))) ->
  store_path handoff_ge (fun after => after = m)
    (Returnstate (number_code parsed)
      (handoff_numeric_cont code bad loaded getter getter_expression wanted_expression e le k) m)
    (match parsed with None => 6%nat | Some _ => 12%nat end)
    (State EntrySource.f_guest
      (if handoff_numeric_bad parsed wanted then handoff_numeric_failure else Sskip) k e
      (handoff_numeric_env code bad loaded getter le parsed wanted getter_value) m).
Proof.
  intros DISTINCT ENCODED LOAD GETTER WANTED COMPARE; destruct parsed as [value|].
  - unfold handoff_numeric_cont, handoff_numeric_choose, handoff_numeric_reject,
      handoff_numeric_bad, handoff_numeric_env; cbn [number_code].
    handoff_route; handoff_route.
    eapply store_next; [reflexivity|apply certified_if_edge with (v := Vint Int.zero) (b := false)|].
    + apply old_expression_value; apply value_temp; apply PTree.gss.
    + reflexivity.
    + handoff_route; handoff_set.
      * eapply location_read_value; [apply local_location_value; exact ENCODED|].
        eapply deref_loc_value; [reflexivity|apply LOAD; reflexivity].
      * handoff_route; handoff_route; handoff_set.
        -- apply GETTER; reflexivity.
        -- handoff_route; handoff_set.
           ++ eapply cast_expression_value.
              ** eapply binary_expression_value.
                 --- apply old_expression_value; apply value_temp.
                     rewrite PTree.gso by congruence; apply PTree.gss.
                 --- apply WANTED; reflexivity.
                 --- apply COMPARE; reflexivity.
              ** apply number_bool_cast.
           ++ handoff_route.
              eapply store_next; [reflexivity|apply certified_if_edge with
                (v := Val.of_bool (negb (value =? wanted))) (b := negb (value =? wanted))|].
              ** apply old_expression_value; apply value_temp; apply PTree.gss.
              ** apply number_bool_value.
              ** apply store_done; reflexivity.
  - unfold handoff_numeric_cont, handoff_numeric_choose, handoff_numeric_reject,
      handoff_numeric_bad, handoff_numeric_env; cbn [number_code].
    handoff_route; handoff_route.
    eapply store_next; [reflexivity|apply certified_if_edge with (v := Vint Int.mone) (b := true)|].
    + apply old_expression_value; apply value_temp; apply PTree.gss.
    + reflexivity.
    + handoff_set.
      * apply old_expression_value; apply value_int.
      * handoff_route.
        eapply store_next; [reflexivity|apply certified_if_edge with (v := Vint Int.one) (b := true)|].
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- reflexivity.
        -- apply store_done; reflexivity.
Qed.

Lemma handoff_numeric_compare_long ge m value wanted :
  0 <= value <= Int64.max_unsigned -> 0 <= wanted <= Int64.max_unsigned ->
  sem_binary_operation ge One (Vlong (Int64.repr value)) tulong
    (Vlong (Int64.repr wanted)) tulong m = Some (Val.of_bool (negb (value =? wanted))).
Proof.
  intros VALUE WANTED.
  change (Some (Val.of_bool (negb (Int64.eq (Int64.repr value) (Int64.repr wanted)))) =
    Some (Val.of_bool (negb (value =? wanted)))).
  unfold Int64.eq; rewrite !Int64.unsigned_repr by assumption.
  destruct (zeq value wanted).
  - rewrite (proj2 (Z.eqb_eq value wanted) e); reflexivity.
  - rewrite (proj2 (Z.eqb_neq value wanted) n); reflexivity.
Qed.

Lemma handoff_numeric_compare_uint ge m value wanted :
  0 <= value <= Int64.max_unsigned -> 0 <= wanted <= Int.max_unsigned ->
  sem_binary_operation ge One (Vlong (Int64.repr value)) tulong
    (Vint (Int.repr wanted)) tuint m = Some (Val.of_bool (negb (value =? wanted))).
Proof.
  intros VALUE WANTED.
  change (Some (Val.of_bool (negb (Int64.eq (Int64.repr value)
    (Int64.repr (Int.unsigned (Int.repr wanted)))))) =
    Some (Val.of_bool (negb (value =? wanted)))).
  rewrite Int.unsigned_repr by exact WANTED.
  apply handoff_numeric_compare_long with (ge := ge) (m := m); [exact VALUE|].
  change Int.max_unsigned with 4294967295 in WANTED.
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma handoff_numeric_good parsed wanted :
  handoff_numeric_bad parsed wanted = false <-> parsed = Some wanted.
Proof.
  destruct parsed as [value|]; cbn [handoff_numeric_bad].
  - rewrite Bool.negb_false_iff, Z.eqb_eq; split; intros SAME; congruence.
  - split; discriminate.
Qed.

From LeanImport Require Import Lean.
Require Import ArgumentsImport ArgumentValues.
From EntryNative Require Import NativeValues.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Theorem handoff_numeric_same_bytes bytes wanted limit decoded :
  decimal_number bytes = Some wanted ->
  Lean.eq (LeanCage_Entry_Arguments_unsigned limit (argument_bytes bytes))
    (Option_some_inst1 Lean.Nat decoded) ->
  Z.of_nat (nat_of_Nat decoded) = wanted.
Proof.
  intros PARSED DECODED.
  destruct (proj1 (decimal_number_exact bytes wanted) PARSED) as [_ [DIGITS [VALUE RANGE]]].
  rewrite (argument_unsigned_value _ _ _ DECODED), argument_fold_native by exact DIGITS.
  symmetry; exact VALUE.
Qed.

Definition handoff_numeric_program code bad loaded getter text_expression getter_expression wanted_expression :=
  Ssequence
    (Ssequence
      (Scall (Some code)
        (Evar EntrySource._number (Tfunction [tptr tschar;tptr tulong] tint cc_default))
        [text_expression; Eaddrof (Evar EntrySource._encoded tulong) (tptr tulong)])
      (handoff_numeric_choose code bad loaded getter getter_expression wanted_expression))
    (handoff_numeric_reject bad).

Definition handoff_uid_getter := Evar EntrySource._run_uid tuint.
Definition handoff_uid_comparison := Etempvar EntrySource._t'39 tuint.
Definition handoff_fd_text :=
  Ederef (Ebinop Oadd (Evar EntrySource._numbers (tarray (tarray tschar 32) 4))
    (Etempvar EntrySource._i tuint) (tptr (tarray tschar 32))) (tarray tschar 32).
Definition handoff_fd_getter :=
  Ederef (Ebinop Oadd (Evar EntrySource._handles (tarray tint 4))
    (Etempvar EntrySource._i tuint) (tptr tint)) tint.
Definition handoff_fd_comparison := Ecast (Etempvar EntrySource._t'33 tint) tulong.

Theorem handoff_uid_numeric_actual : guest_phase 8 =
  handoff_numeric_program EntrySource._t'7 EntrySource._t'8 EntrySource._t'38 EntrySource._t'39
    (Evar EntrySource._uid (tarray tschar 32)) handoff_uid_getter handoff_uid_comparison.
Proof. reflexivity. Qed.

Definition handoff_numeric_node code body :=
  match body with
  | Ssequence (Ssequence (Scall (Some found) (Evar function _) _) _) _ =>
      Pos.eqb found code && Pos.eqb function EntrySource._number
  | _ => false
  end.

Definition handoff_numeric_found (left right : option statement) :=
  match left with Some _ => left | None => right end.
Fixpoint handoff_find_numeric code body : option statement :=
  if handoff_numeric_node code body then Some body else
  match body with
  | Ssequence first second | Sloop first second =>
      handoff_numeric_found (handoff_find_numeric code first) (handoff_find_numeric code second)
  | Sifthenelse _ yes no =>
      handoff_numeric_found (handoff_find_numeric code yes) (handoff_find_numeric code no)
  | Slabel _ statement => handoff_find_numeric code statement
  | _ => None
  end.

Definition handoff_fd_numeric :=
  match handoff_find_numeric EntrySource._t'13 (fn_body EntrySource.f_guest) with
  | Some statement => statement | None => Sskip
  end.

Theorem handoff_fd_numeric_actual : handoff_fd_numeric =
  handoff_numeric_program EntrySource._t'13 EntrySource._t'14 EntrySource._t'32 EntrySource._t'33
    handoff_fd_text handoff_fd_getter handoff_fd_comparison.
Proof. reflexivity. Qed.

Lemma handoff_number_binding :
  Genv.find_symbol handoff_ge EntrySource._number = Some (handoff_symbol EntrySource._number) /\
  Genv.find_funct handoff_ge (Vptr (handoff_symbol EntrySource._number) Ptrofs.zero) =
    Some (Internal EntrySource.f_number).
Proof. split; reflexivity. Qed.

Lemma handoff_encoded_address_value e le m encoded :
  e ! EntrySource._encoded = Some (encoded,tulong) ->
  expression_value handoff_ge e le m (Eaddrof (Evar EntrySource._encoded tulong) (tptr tulong))
    (Vptr encoded Ptrofs.zero).
Proof.
  intros LOCAL.
  apply LeanCageMain.MainValues.main_address_value; apply local_location_value; exact LOCAL.
Qed.

Theorem handoff_numeric_call_source e le m k code bad loaded getter
    text_expression getter_expression wanted_expression input offset encoded :
  e ! EntrySource._number = None -> e ! EntrySource._encoded = Some (encoded,tulong) ->
  typeof text_expression = tarray tschar 32 ->
  expression_value handoff_ge e le m text_expression (Vptr input offset) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest
      (handoff_numeric_program code bad loaded getter text_expression getter_expression wanted_expression)
      k e le m) 3
    (Callstate (Internal EntrySource.f_number) [Vptr input offset; Vptr encoded Ptrofs.zero]
      (handoff_numeric_cont code bad loaded getter getter_expression wanted_expression e le k) m).
Proof.
  intros GLOBAL ENCODED TEXTTYPE TEXT; unfold handoff_numeric_program.
  handoff_route; handoff_route.
  eapply store_next; [reflexivity| |].
  - eapply certified_call_edge.
    + reflexivity.
    + apply old_expression_value; eapply value_function;
        [exact GLOBAL|exact (proj1 handoff_number_binding)|reflexivity].
    + eapply cons_argument_values.
      * exact TEXT.
      * rewrite TEXTTYPE; reflexivity.
      * eapply cons_argument_values.
        -- apply handoff_encoded_address_value; exact ENCODED.
        -- reflexivity.
        -- apply no_argument_values.
    + exact (proj2 handoff_number_binding).
    + reflexivity.
  - apply store_done; reflexivity.
Qed.

Lemma handoff_uid_binding :
  Genv.find_symbol handoff_ge EntrySource._run_uid = Some (handoff_symbol EntrySource._run_uid).
Proof. reflexivity. Qed.

Lemma handoff_native_array_index_unsigned ge m output element count stride index :
  sizeof ge element = stride -> 0 <= stride <= 592 -> 0 <= index <= 74 ->
  sem_binary_operation ge Oadd (Vptr output Ptrofs.zero) (tarray element count)
    (Vint (Int.repr index)) tuint m = Some (Vptr output (Ptrofs.repr (stride * index))).
Proof.
  intros SIZE STRIDE INDEX.
  change (Some (Vptr output (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr (sizeof ge element)) (Ptrofs.of_intu (Int.repr index))))) =
    Some (Vptr output (Ptrofs.repr (stride * index)))).
  rewrite SIZE; unfold Ptrofs.of_intu, Ptrofs.of_int; rewrite Int.unsigned_repr
    by (change Int.max_unsigned with 4294967295; lia).
  rewrite Ptrofs.add_zero_l, Ptrofs.mul_signed, !Ptrofs.signed_repr
    by (change Ptrofs.min_signed with (-9223372036854775808);
      change Ptrofs.max_signed with 9223372036854775807; nia).
  reflexivity.
Qed.

Theorem handoff_uid_return_source e le m k encoded parsed wanted :
  e ! EntrySource._encoded = Some (encoded,tulong) ->
  e ! EntrySource._run_uid = None ->
  Mem.loadv Mint32 m (Vptr (handoff_symbol EntrySource._run_uid) Ptrofs.zero) = Some (Vint (Int.repr wanted)) ->
  0 <= wanted <= Int.max_unsigned ->
  (forall value, parsed = Some value -> 0 <= value <= Int64.max_unsigned) ->
  (forall value, parsed = Some value ->
    Mem.loadv Mint64 m (Vptr encoded Ptrofs.zero) = Some (Vlong (Int64.repr value))) ->
  store_path handoff_ge (fun after => after = m)
    (Returnstate (number_code parsed)
      (handoff_numeric_cont EntrySource._t'7 EntrySource._t'8 EntrySource._t'38 EntrySource._t'39
        handoff_uid_getter handoff_uid_comparison e le k) m)
    (match parsed with None => 6%nat | Some _ => 12%nat end)
    (State EntrySource.f_guest
      (if handoff_numeric_bad parsed wanted then handoff_numeric_failure else Sskip) k e
      (handoff_numeric_env EntrySource._t'7 EntrySource._t'8 EntrySource._t'38 EntrySource._t'39
        le parsed wanted (Vint (Int.repr wanted))) m).
Proof.
  intros ENCODED GLOBAL UID BOUND RANGE LOAD.
  eapply handoff_numeric_return_source with (comparison_value := Vint (Int.repr wanted)).
  - discriminate.
  - exact ENCODED.
  - exact LOAD.
  - intros value PARSED; unfold handoff_uid_getter.
    eapply location_read_value; [apply global_location_value; [exact GLOBAL|apply handoff_uid_binding]|].
    eapply deref_loc_value; [reflexivity|exact UID].
  - intros value PARSED; unfold handoff_uid_comparison.
    apply old_expression_value; apply value_temp; apply PTree.gss.
  - intros value PARSED; apply handoff_numeric_compare_uint; [apply RANGE; exact PARSED|exact BOUND].
Qed.

Lemma handoff_signed_to_long m value : 0 <= value <= Int.max_signed ->
  sem_cast (Vint (Int.repr value)) tint tulong m = Some (Vlong (Int64.repr value)).
Proof.
  intros VALUE.
  change (Some (Vlong (Int64.repr (Int.signed (Int.repr value)))) = Some (Vlong (Int64.repr value))).
  rewrite Int.signed_repr by (change Int.min_signed with (-2147483648); lia); reflexivity.
Qed.

Theorem handoff_fd_return_source e le m k encoded handles index parsed wanted :
  e ! EntrySource._encoded = Some (encoded,tulong) ->
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * index))) = Some (Vint (Int.repr wanted)) ->
  4 <= wanted <= Int.max_signed ->
  (forall value, parsed = Some value -> 0 <= value <= Int64.max_unsigned) ->
  (forall value, parsed = Some value ->
    Mem.loadv Mint64 m (Vptr encoded Ptrofs.zero) = Some (Vlong (Int64.repr value))) ->
  store_path handoff_ge (fun after => after = m)
    (Returnstate (number_code parsed)
      (handoff_numeric_cont EntrySource._t'13 EntrySource._t'14 EntrySource._t'32 EntrySource._t'33
        handoff_fd_getter handoff_fd_comparison e le k) m)
    (match parsed with None => 6%nat | Some _ => 12%nat end)
    (State EntrySource.f_guest
      (if handoff_numeric_bad parsed wanted then handoff_numeric_failure else Sskip) k e
      (handoff_numeric_env EntrySource._t'13 EntrySource._t'14 EntrySource._t'32 EntrySource._t'33
        le parsed wanted (Vint (Int.repr wanted))) m).
Proof.
  intros ENCODED LOCAL INDEX INDEXBOUND DESCRIPTOR BOUND RANGE LOAD.
  eapply handoff_numeric_return_source with (comparison_value := Vlong (Int64.repr wanted)).
  - discriminate.
  - exact ENCODED.
  - exact LOAD.
  - intros value PARSED; unfold handoff_fd_getter.
    eapply location_read_value.
    + apply pointer_location_value; eapply binary_expression_value.
      * apply handoff_array_value; exact LOCAL.
      * apply old_expression_value; apply value_temp; WriteAll.lookup.
      * apply handoff_native_array_index_unsigned with (stride := 4) (index := index);
          [reflexivity|lia|lia].
    + eapply deref_loc_value; [reflexivity|exact DESCRIPTOR].
  - intros value PARSED; unfold handoff_fd_comparison; eapply cast_expression_value.
    + apply old_expression_value; apply value_temp; apply PTree.gss.
    + apply handoff_signed_to_long; lia.
  - intros value PARSED; apply handoff_numeric_compare_long; [apply RANGE; exact PARSED|].
    change Int.max_signed with 2147483647 in BOUND.
    change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma handoff_number_post_word before encoded parsed after value :
  number_post before encoded Ptrofs.zero parsed after -> parsed = Some value ->
  Mem.loadv Mint64 after (Vptr encoded Ptrofs.zero) = Some (Vlong (Int64.repr value)).
Proof.
  intros POST PARSED; subst parsed.
  change (Mem.store Mint64 before encoded 0 (Vlong (Int64.repr value)) = Some after) in POST.
  change (Mem.load Mint64 after encoded 0 = Some (Vlong (Int64.repr value))).
  rewrite (Mem.load_store_same _ _ _ _ _ _ POST); reflexivity.
Qed.

Lemma handoff_number_post_load_other before encoded parsed after chunk block offset :
  number_post before encoded Ptrofs.zero parsed after -> block <> encoded ->
  Mem.loadv chunk after (Vptr block offset) = Mem.loadv chunk before (Vptr block offset).
Proof.
  destruct parsed as [value|]; cbn [number_post]; intros POST DIFFERENT; [|subst; reflexivity].
  change (Mem.store Mint64 before encoded 0 (Vlong (Int64.repr value)) = Some after) in POST.
  unfold Mem.loadv; destruct (zle _ _); [|reflexivity].
  eapply Mem.load_store_other; [exact POST|left; exact DIFFERENT].
Qed.

Lemma handoff_number_post_input before encoded parsed after block offset bytes :
  number_post before encoded Ptrofs.zero parsed after -> block <> encoded ->
  number_input before block offset bytes -> number_input after block offset bytes.
Proof.
  destruct parsed as [value|]; cbn [number_post]; intros POST DIFFERENT INPUT; [|subst; exact INPUT].
  change (Mem.store Mint64 before encoded 0 (Vlong (Int64.repr value)) = Some after) in POST.
  destruct INPUT as [BOUND [NONZERO LOAD]]; split; [exact BOUND|]. split; [exact NONZERO|].
  rewrite (Mem.loadbytes_store_other _ _ _ _ _ _ POST) by auto; exact LOAD.
Qed.

Lemma handoff_decimal_some_range bytes value :
  decimal_number bytes = Some value -> 0 <= value <= Int64.max_unsigned.
Proof.
  intros PARSED; destruct (proj1 (decimal_number_exact bytes value) PARSED) as [_ [_ [_ RANGE]]].
  change Int64.max_unsigned with decimal_max; exact RANGE.
Qed.

Theorem handoff_uid_numeric_source e le before k uid encoded bytes wanted :
  e ! EntrySource._uid = Some (uid,tarray tschar 32) ->
  e ! EntrySource._encoded = Some (encoded,tulong) ->
  e ! EntrySource._number = None -> e ! EntrySource._run_uid = None ->
  handoff_symbol EntrySource._run_uid <> encoded -> uid <> encoded ->
  Mem.loadv Mint32 before (Vptr (handoff_symbol EntrySource._run_uid) Ptrofs.zero) = Some (Vint (Int.repr wanted)) ->
  0 <= wanted <= Int.max_unsigned ->
  number_input before uid Ptrofs.zero bytes -> number_output before encoded Ptrofs.zero ->
  exists count after,
    (count <= 100 * length bytes + 115)%nat /\
    number_post before encoded Ptrofs.zero (decimal_number bytes) after /\
    number_input after uid Ptrofs.zero bytes /\
    store_path handoff_ge (number_memory before encoded Ptrofs.zero (decimal_number bytes))
      (State EntrySource.f_guest (guest_phase 8) k e le before) count
      (State EntrySource.f_guest
        (if handoff_numeric_bad (decimal_number bytes) wanted then handoff_numeric_failure else Sskip) k e
        (handoff_numeric_env EntrySource._t'7 EntrySource._t'8 EntrySource._t'38 EntrySource._t'39
          le (decimal_number bytes) wanted (Vint (Int.repr wanted))) after).
Proof.
  intros UID ENCODED NUMBER GLOBAL DIFFERENT BUFFER VALUE BOUND INPUT OUTPUT.
  set (continuation := handoff_numeric_cont EntrySource._t'7 EntrySource._t'8 EntrySource._t'38 EntrySource._t'39
    handoff_uid_getter handoff_uid_comparison e le k).
  destruct (handoff_number_source_bound handoff_ge before uid Ptrofs.zero bytes encoded Ptrofs.zero continuation INPUT OUTPUT)
    as [count [after [COUNTBOUND [POST PATH]]]].
  exists (3 + count + (match decimal_number bytes with None => 6 | Some _ => 12 end))%nat,after.
  split; [destruct (decimal_number bytes); lia|].
  split; [exact POST|]. split.
  - eapply handoff_number_post_input; eassumption.
  - rewrite handoff_uid_numeric_actual.
    eapply store_path_trans with (n := 3%nat).
    + eapply number_path_implication with (P := fun current => current = before).
      * intros current SAME; subst; apply number_memory_initial.
      * apply handoff_numeric_call_source with (input := uid) (offset := Ptrofs.zero) (encoded := encoded);
          try assumption; [reflexivity|apply handoff_array_value; exact UID].
    + eapply store_path_trans with (n := count).
      * exact PATH.
      * eapply number_path_implication with (P := fun current => current = after).
        -- intros current SAME; subst; right; exact POST.
        -- apply handoff_uid_return_source with (encoded := encoded).
           ++ exact ENCODED.
           ++ exact GLOBAL.
           ++ rewrite (handoff_number_post_load_other _ _ _ _ _ _ _ POST DIFFERENT); exact VALUE.
           ++ exact BOUND.
           ++ intros value PARSED; apply handoff_decimal_some_range with (bytes := bytes); exact PARSED.
           ++ intros value PARSED; eapply handoff_number_post_word; eassumption.
Qed.

Lemma handoff_fd_text_value e le m numbers index :
  e ! EntrySource._numbers = Some (numbers,tarray (tarray tschar 32) 4) ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  expression_value handoff_ge e le m handoff_fd_text (Vptr numbers (Ptrofs.repr (32 * index))).
Proof.
  intros LOCAL INDEX BOUND; unfold handoff_fd_text.
  eapply location_read_value.
  - apply pointer_location_value; eapply binary_expression_value.
    + apply handoff_array_value; exact LOCAL.
    + apply old_expression_value; apply value_temp; exact INDEX.
    + apply handoff_native_array_index_unsigned with (stride := 32) (index := index);
        [reflexivity|lia|lia].
  - apply deref_loc_reference; reflexivity.
Qed.

Theorem handoff_fd_numeric_source e le before k numbers encoded handles index bytes wanted :
  e ! EntrySource._numbers = Some (numbers,tarray (tarray tschar 32) 4) ->
  e ! EntrySource._encoded = Some (encoded,tulong) ->
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  e ! EntrySource._number = None -> handles <> encoded -> numbers <> encoded ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  Mem.loadv Mint32 before (Vptr handles (Ptrofs.repr (4 * index))) = Some (Vint (Int.repr wanted)) ->
  4 <= wanted <= Int.max_signed ->
  number_input before numbers (Ptrofs.repr (32 * index)) bytes -> number_output before encoded Ptrofs.zero ->
  exists count after,
    (count <= 100 * length bytes + 115)%nat /\
    number_post before encoded Ptrofs.zero (decimal_number bytes) after /\
    number_input after numbers (Ptrofs.repr (32 * index)) bytes /\
    store_path handoff_ge (number_memory before encoded Ptrofs.zero (decimal_number bytes))
      (State EntrySource.f_guest handoff_fd_numeric k e le before) count
      (State EntrySource.f_guest
        (if handoff_numeric_bad (decimal_number bytes) wanted then handoff_numeric_failure else Sskip) k e
        (handoff_numeric_env EntrySource._t'13 EntrySource._t'14 EntrySource._t'32 EntrySource._t'33
          le (decimal_number bytes) wanted (Vint (Int.repr wanted))) after).
Proof.
  intros NUMBERS ENCODED HANDLES NUMBER DIFFERENT BUFFER INDEX INDEXBOUND VALUE BOUND INPUT OUTPUT.
  set (continuation := handoff_numeric_cont EntrySource._t'13 EntrySource._t'14 EntrySource._t'32 EntrySource._t'33
    handoff_fd_getter handoff_fd_comparison e le k).
  destruct (handoff_number_source_bound handoff_ge before numbers (Ptrofs.repr (32 * index)) bytes encoded Ptrofs.zero
    continuation INPUT OUTPUT) as [count [after [COUNTBOUND [POST PATH]]]].
  exists (3 + count + (match decimal_number bytes with None => 6 | Some _ => 12 end))%nat,after.
  split; [destruct (decimal_number bytes); lia|].
  split; [exact POST|]. split.
  - eapply handoff_number_post_input; eassumption.
  - rewrite handoff_fd_numeric_actual.
    eapply store_path_trans with (n := 3%nat).
    + eapply number_path_implication with (P := fun current => current = before).
      * intros current SAME; subst; apply number_memory_initial.
      * apply handoff_numeric_call_source with (input := numbers) (offset := Ptrofs.repr (32 * index)) (encoded := encoded);
          try assumption; [reflexivity|apply handoff_fd_text_value; assumption].
    + eapply store_path_trans with (n := count).
      * exact PATH.
      * eapply number_path_implication with (P := fun current => current = after).
        -- intros current SAME; subst; right; exact POST.
        -- apply handoff_fd_return_source with (encoded := encoded) (handles := handles) (index := index).
           ++ exact ENCODED.
           ++ exact HANDLES.
           ++ exact INDEX.
           ++ exact INDEXBOUND.
           ++ rewrite (handoff_number_post_load_other _ _ _ _ _ _ _ POST DIFFERENT); exact VALUE.
           ++ exact BOUND.
           ++ intros value PARSED; apply handoff_decimal_some_range with (bytes := bytes); exact PARSED.
           ++ intros value PARSED; eapply handoff_number_post_word; eassumption.
Qed.
