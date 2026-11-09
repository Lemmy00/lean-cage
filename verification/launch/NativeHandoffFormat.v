(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The source passes the real UID/descriptor value and checks returned buffer extent. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure
  NativeHandoffArguments NativeHandoffNumeric.
From LeanCageMainNumber Require Import NumberControl.
Import ListNotations.
Open Scope Z_scope.

Definition handoff_format_program getter code text_expression getter_expression value_expression :=
  Ssequence
    (Ssequence (Sset getter getter_expression)
      (Scall (Some code)
        (Evar EntrySource._entry_decimal (Tfunction [tptr tschar;tulong] tint cc_default))
        [text_expression; value_expression]))
    (Sset EntrySource._count (Etempvar code tint)).

Definition handoff_format_cont getter code getter_value e le k :=
  Kcall (Some code) EntrySource.f_guest e (PTree.set getter getter_value le)
    (Kseq (Sset EntrySource._count (Etempvar code tint)) k).

Definition handoff_format_env getter code getter_value le returned :=
  PTree.set EntrySource._count (Vint returned)
    (PTree.set code (Vint returned) (PTree.set getter getter_value le)).

Lemma handoff_decimal_binding :
  Genv.find_symbol handoff_ge EntrySource._entry_decimal = Some (handoff_symbol EntrySource._entry_decimal) /\
  Genv.find_funct handoff_ge (Vptr (handoff_symbol EntrySource._entry_decimal) Ptrofs.zero) =
    Some entry_decimal_definition.
Proof. split; reflexivity. Qed.

Theorem handoff_format_call_source e le m k getter code text_expression getter_expression value_expression
    output offset wanted getter_value argument_value :
  e ! EntrySource._entry_decimal = None ->
  typeof text_expression = tarray tschar 32 ->
  expression_value handoff_ge e le m getter_expression getter_value ->
  expression_value handoff_ge e (PTree.set getter getter_value le) m text_expression (Vptr output offset) ->
  expression_value handoff_ge e (PTree.set getter getter_value le) m value_expression argument_value ->
  sem_cast argument_value (typeof value_expression) tulong m = Some (Vlong (Int64.repr wanted)) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest (handoff_format_program getter code text_expression getter_expression value_expression)
      k e le m) 5
    (Callstate entry_decimal_definition [Vptr output offset; Vlong (Int64.repr wanted)]
      (handoff_format_cont getter code getter_value e le k) m).
Proof.
  intros GLOBAL TEXTTYPE GETTER TEXT VALUE CAST; unfold handoff_format_program.
  handoff_route; handoff_route; handoff_set.
  - exact GETTER.
  - handoff_route.
    eapply store_next; [reflexivity| |].
    + eapply certified_call_edge.
      * reflexivity.
      * apply old_expression_value; eapply value_function;
          [exact GLOBAL|exact (proj1 handoff_decimal_binding)|reflexivity].
      * eapply cons_argument_values.
        -- exact TEXT.
        -- rewrite TEXTTYPE; reflexivity.
        -- eapply cons_argument_values; [exact VALUE|exact CAST|apply no_argument_values].
      * exact (proj2 handoff_decimal_binding).
      * reflexivity.
    + apply store_done; reflexivity.
Qed.

Theorem handoff_format_return_source e le m k getter code getter_value returned :
  code <> EntrySource._count ->
  store_path handoff_ge (fun after => after = m)
    (Returnstate (Vint returned) (handoff_format_cont getter code getter_value e le k) m) 3
    (State EntrySource.f_guest Sskip k e (handoff_format_env getter code getter_value le returned) m).
Proof.
  intros DISTINCT; unfold handoff_format_cont, handoff_format_env.
  handoff_route; handoff_route; handoff_set.
  - apply old_expression_value; apply value_temp; apply PTree.gss.
  - apply store_done; reflexivity.
Qed.

Theorem handoff_uid_format_actual : guest_phase 6 =
  handoff_format_program EntrySource._t'40 EntrySource._t'3
    (Evar EntrySource._uid (tarray tschar 32)) handoff_uid_getter (Etempvar EntrySource._t'40 tuint).
Proof. reflexivity. Qed.

Theorem handoff_uid_format_call_source e le m k uid wanted :
  e ! EntrySource._entry_decimal = None -> e ! EntrySource._run_uid = None ->
  e ! EntrySource._uid = Some (uid,tarray tschar 32) ->
  Mem.loadv Mint32 m (Vptr (handoff_symbol EntrySource._run_uid) Ptrofs.zero) = Some (Vint (Int.repr wanted)) ->
  0 <= wanted <= Int.max_unsigned ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest (guest_phase 6) k e le m) 5
    (Callstate entry_decimal_definition [Vptr uid Ptrofs.zero; Vlong (Int64.repr wanted)]
      (handoff_format_cont EntrySource._t'40 EntrySource._t'3 (Vint (Int.repr wanted)) e le k) m).
Proof.
  intros DECIMAL GLOBAL LOCAL UID BOUND; rewrite handoff_uid_format_actual.
  eapply handoff_format_call_source with (argument_value := Vint (Int.repr wanted)).
  - exact DECIMAL.
  - reflexivity.
  - unfold handoff_uid_getter; eapply location_read_value;
      [apply global_location_value; [exact GLOBAL|apply handoff_uid_binding]|].
    eapply deref_loc_value; [reflexivity|exact UID].
  - apply handoff_array_value; exact LOCAL.
  - apply old_expression_value; apply value_temp; apply PTree.gss.
  - change (Some (Vlong (Int64.repr (Int.unsigned (Int.repr wanted)))) = Some (Vlong (Int64.repr wanted))).
    rewrite Int.unsigned_repr by exact BOUND; reflexivity.
Qed.

Definition handoff_count_bad returned :=
  if Int.signed returned <=? 0 then true else 32 <=? Int.signed returned.

Definition handoff_count_choose bad :=
  Sifthenelse (Ebinop Ole (Etempvar EntrySource._count tint) (Econst_int Int.zero tint) tint)
    (Sset bad (Econst_int Int.one tint))
    (Sset bad (Ecast
      (Ebinop Oge (Ecast (Etempvar EntrySource._count tint) tulong)
        (Esizeof (tarray tschar 32) tulong) tint) tbool)).

Lemma handoff_count_lower ge m returned :
  sem_binary_operation ge Ole (Vint returned) tint (Vint Int.zero) tint m =
    Some (Val.of_bool (Int.signed returned <=? 0)).
Proof.
  change (Some (Val.of_bool (negb (Int.lt Int.zero returned))) =
    Some (Val.of_bool (Int.signed returned <=? 0))).
  unfold Int.lt; change (Some (Val.of_bool (negb (if zlt 0 (Int.signed returned) then true else false))) =
    Some (Val.of_bool (Int.signed returned <=? 0))).
  destruct (zlt 0 (Int.signed returned)).
  - rewrite (proj2 (Z.leb_gt (Int.signed returned) 0) ltac:(lia)); reflexivity.
  - rewrite (proj2 (Z.leb_le (Int.signed returned) 0) ltac:(lia)); reflexivity.
Qed.

Lemma handoff_size32_value e le m :
  expression_value handoff_ge e le m (Esizeof (tarray tschar 32) tulong) (Vlong (Int64.repr 32)).
Proof.
  split; [constructor|]. intros other EVALUATION; inversion EVALUATION; subst; [reflexivity|].
  match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV end.
Qed.

Lemma handoff_count_upper ge m value : 0 <= value <= Int64.max_unsigned ->
  sem_binary_operation ge Oge (Vlong (Int64.repr value)) tulong (Vlong (Int64.repr 32)) tulong m =
    Some (Val.of_bool (32 <=? value)).
Proof.
  intros VALUE.
  change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr value) (Int64.repr 32)))) =
    Some (Val.of_bool (32 <=? value))).
  unfold Int64.ltu; rewrite (Int64.unsigned_repr value) by exact VALUE.
  change (Some (Val.of_bool (negb (if zlt value 32 then true else false))) =
    Some (Val.of_bool (32 <=? value))).
  destruct (zlt value 32).
  - rewrite (proj2 (Z.leb_gt 32 value) ltac:(lia)); reflexivity.
  - rewrite (proj2 (Z.leb_le 32 value) ltac:(lia)); reflexivity.
Qed.

Theorem handoff_count_choose_source e le m k bad returned :
  le ! EntrySource._count = Some (Vint returned) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest (handoff_count_choose bad) k e le m) 2
    (State EntrySource.f_guest Sskip k e (PTree.set bad (Val.of_bool (handoff_count_bad returned)) le) m).
Proof.
  intros COUNT; unfold handoff_count_choose, handoff_count_bad.
  destruct (Int.signed returned <=? 0) eqn:LOW.
  - eapply store_next; [reflexivity|apply certified_if_edge with (v := Val.of_bool true) (b := true)|].
    + eapply binary_expression_value.
      * apply old_expression_value; apply value_temp; exact COUNT.
      * apply old_expression_value; apply value_int.
      * rewrite handoff_count_lower, LOW; reflexivity.
    + reflexivity.
    + handoff_set; [apply old_expression_value; apply value_int|apply store_done; reflexivity].
  - eapply store_next; [reflexivity|apply certified_if_edge with (v := Val.of_bool false) (b := false)|].
    + eapply binary_expression_value.
      * apply old_expression_value; apply value_temp; exact COUNT.
      * apply old_expression_value; apply value_int.
      * rewrite handoff_count_lower, LOW; reflexivity.
    + reflexivity.
    + handoff_set.
      * eapply cast_expression_value.
        -- eapply binary_expression_value.
           ++ eapply cast_expression_value.
              ** apply old_expression_value; apply value_temp; exact COUNT.
              ** reflexivity.
           ++ apply handoff_size32_value.
           ++ apply handoff_count_upper.
              apply Z.leb_gt in LOW; pose proof (Int.signed_range returned).
              change Int.max_signed with 2147483647 in H.
              change Int64.max_unsigned with 18446744073709551615; lia.
        -- apply number_bool_cast.
      * apply store_done; reflexivity.
Qed.

Lemma handoff_count_good returned : handoff_count_bad returned = false <-> 0 < Int.signed returned < 32.
Proof.
  unfold handoff_count_bad; destruct (Int.signed returned <=? 0) eqn:LOW.
  - apply Z.leb_le in LOW; split; [discriminate|lia].
  - apply Z.leb_gt in LOW; rewrite Z.leb_gt; lia.
Qed.

Definition handoff_count_error returned selected :=
  Sifthenelse (Ebinop Olt (Etempvar EntrySource._count tint) (Econst_int Int.zero tint) tint)
    (Ssequence
      (Scall (Some returned) (Evar EntrySource._error_number (Tfunction [] tint cc_default)) [])
      (Sset selected (Ecast (Etempvar returned tint) tint)))
    (Sset selected (Ecast (Econst_int (Int.repr 75) tint) tint)).

Definition handoff_count_failure selected :=
  Scall None (Evar EntrySource._fail_child (Tfunction [tint;tuint;tint] tvoid cc_default))
    [Etempvar EntrySource._failure tint; Econst_int Int.one tint; Etempvar selected tint].

Definition handoff_count_reject bad returned selected :=
  Sifthenelse (Etempvar bad tint)
    (Ssequence (handoff_count_error returned selected) (handoff_count_failure selected)) Sskip.

Definition handoff_count_program bad returned selected :=
  Ssequence (handoff_count_choose bad) (handoff_count_reject bad returned selected).

Theorem handoff_uid_count_actual : guest_phase 7 =
  handoff_count_program EntrySource._t'6 EntrySource._t'5 EntrySource._t'4.
Proof. reflexivity. Qed.

Definition handoff_find_format_node code body :=
  match body with
  | Ssequence (Ssequence (Sset _ _) (Scall (Some found) (Evar function _) _)) _ =>
      Pos.eqb found code && Pos.eqb function EntrySource._entry_decimal
  | _ => false
  end.

Fixpoint handoff_find_format code body : option statement :=
  if handoff_find_format_node code body then Some body else
  match body with
  | Ssequence first second | Sloop first second =>
      handoff_numeric_found (handoff_find_format code first) (handoff_find_format code second)
  | Sifthenelse _ yes no =>
      handoff_numeric_found (handoff_find_format code yes) (handoff_find_format code no)
  | Slabel _ statement => handoff_find_format code statement
  | _ => None
  end.

Definition handoff_fd_format :=
  match handoff_find_format EntrySource._t'9 (fn_body EntrySource.f_guest) with
  | Some statement => statement | None => Sskip
  end.

Theorem handoff_fd_format_actual : handoff_fd_format =
  handoff_format_program EntrySource._t'34 EntrySource._t'9 handoff_fd_text
    handoff_fd_getter (Ecast (Etempvar EntrySource._t'34 tint) tulong).
Proof. reflexivity. Qed.

Theorem handoff_fd_format_call_source e le m k numbers handles index wanted :
  e ! EntrySource._entry_decimal = None ->
  e ! EntrySource._numbers = Some (numbers,tarray (tarray tschar 32) 4) ->
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4 * index))) = Some (Vint (Int.repr wanted)) ->
  4 <= wanted <= Int.max_signed ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest handoff_fd_format k e le m) 5
    (Callstate entry_decimal_definition
      [Vptr numbers (Ptrofs.repr (32 * index)); Vlong (Int64.repr wanted)]
      (handoff_format_cont EntrySource._t'34 EntrySource._t'9 (Vint (Int.repr wanted)) e le k) m).
Proof.
  intros DECIMAL NUMBERS HANDLES INDEX INDEXBOUND DESCRIPTOR BOUND; rewrite handoff_fd_format_actual.
  eapply handoff_format_call_source with (argument_value := Vlong (Int64.repr wanted)).
  - exact DECIMAL.
  - reflexivity.
  - unfold handoff_fd_getter; eapply location_read_value.
    + apply pointer_location_value; eapply binary_expression_value.
      * apply handoff_array_value; exact HANDLES.
      * apply old_expression_value; apply value_temp; exact INDEX.
      * apply handoff_native_array_index_unsigned with (stride := 4) (index := index);
          [reflexivity|lia|lia].
    + eapply deref_loc_value; [reflexivity|exact DESCRIPTOR].
  - apply handoff_fd_text_value; [exact NUMBERS|WriteAll.lookup|exact INDEXBOUND].
  - eapply cast_expression_value.
    + apply old_expression_value; apply value_temp; apply PTree.gss.
    + apply handoff_signed_to_long; lia.
  - reflexivity.
Qed.

Definition handoff_find_count_node bad body :=
  match body with
  | Ssequence (Sifthenelse _ (Sset found _) _) (Sifthenelse (Etempvar checked _) _ _) =>
      Pos.eqb found bad && Pos.eqb checked bad
  | _ => false
  end.

Fixpoint handoff_find_count bad body : option statement :=
  if handoff_find_count_node bad body then Some body else
  match body with
  | Ssequence first second | Sloop first second =>
      handoff_numeric_found (handoff_find_count bad first) (handoff_find_count bad second)
  | Sifthenelse _ yes no =>
      handoff_numeric_found (handoff_find_count bad yes) (handoff_find_count bad no)
  | Slabel _ statement => handoff_find_count bad statement
  | _ => None
  end.

Definition handoff_fd_count :=
  match handoff_find_count EntrySource._t'12 (fn_body EntrySource.f_guest) with
  | Some statement => statement | None => Sskip
  end.

Theorem handoff_fd_count_actual : handoff_fd_count =
  handoff_count_program EntrySource._t'12 EntrySource._t'11 EntrySource._t'10.
Proof. reflexivity. Qed.
