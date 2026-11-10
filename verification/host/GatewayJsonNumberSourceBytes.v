(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: JSON numeric scans use the actual 65536-byte bound and signed C character loads. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LocalAccess Readers.
From HostGateway Require Import GatewaySource GatewayIntegerMemory GatewayIntegerLoop GatewayIntegerPrefix.
Import ListNotations.
Open Scope Z_scope.

Lemma json_number_word_equal first second :
  0 <= first <= 65536 -> 0 <= second <= 65536 ->
  Int64.eq (Int64.repr first) (Int64.repr second) = Z.eqb first second.
Proof.
  intros FIRST SECOND; destruct (Z.eq_dec first second) as [SAME |DIFFERENT].
  - subst; rewrite Int64.eq_true; symmetry; apply Z.eqb_refl.
  - rewrite Int64.eq_false; [symmetry; apply Z.eqb_neq; exact DIFFERENT |].
    intro SAME; apply (f_equal Int64.unsigned) in SAME.
    rewrite !Int64.unsigned_repr in SAME by (change Int64.max_unsigned with 18446744073709551615; lia); congruence.
Qed.

Lemma json_number_word_less first second :
  0 <= first <= 65536 -> 0 <= second <= 65536 ->
  Int64.ltu (Int64.repr first) (Int64.repr second) = (first <? second).
Proof.
  intros FIRST SECOND; unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (zlt first second); [symmetry; apply Z.ltb_lt |symmetry; apply Z.ltb_ge]; lia.
Qed.

Theorem gateway_json_number_character ge environment parameters memory identifier object index byte :
  0 <= index <= 65536 -> parameters ! _bytes = Some (Vptr object Ptrofs.zero) ->
  parameters ! identifier = Some (Vlong (Int64.repr index)) ->
  Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) = Some (Vint (Int.repr (Byte.signed byte))) ->
  expression_value ge environment parameters memory
    (Ederef (Ebinop Oadd (Etempvar _bytes (tptr tschar)) (Etempvar identifier tulong) (tptr tschar)) tschar)
    (Vint (Int.repr (Byte.signed byte))).
Proof.
  intros INDEX BYTES POSITION LOAD.
  eapply location_read_value with (b := object) (ofs := Ptrofs.repr index).
  - apply pointer_location_value; eapply binary_expression_value with (v := Vptr object Ptrofs.zero) (w := Vlong (Int64.repr index)).
    + apply old_expression_value, value_temp; exact BYTES.
    + apply old_expression_value, value_temp; exact POSITION.
    + change (Some (Vptr object (Ptrofs.add Ptrofs.zero (Ptrofs.mul Ptrofs.one (Ptrofs.of_int64 (Int64.repr index))))) =
        Some (Vptr object (Ptrofs.repr index))).
      rewrite Ptrofs.add_zero_l, Ptrofs.mul_commut, Ptrofs.mul_one.
      unfold Ptrofs.of_int64; rewrite Int64.unsigned_repr by
        (change Int64.max_unsigned with 18446744073709551615; lia); reflexivity.
  - apply deref_loc_value with (chunk := Mint8signed); [reflexivity |exact LOAD].
Qed.

Theorem gateway_json_number_fixed_character ge environment parameters memory object index byte :
  0 <= index <= 65536 -> parameters ! _bytes = Some (Vptr object Ptrofs.zero) ->
  Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) = Some (Vint (Int.repr (Byte.signed byte))) ->
  expression_value ge environment parameters memory
    (Ederef (Ebinop Oadd (Etempvar _bytes (tptr tschar)) (Econst_int (Int.repr index) tint) (tptr tschar)) tschar)
    (Vint (Int.repr (Byte.signed byte))).
Proof.
  intros INDEX BYTES LOAD.
  eapply location_read_value with (b := object) (ofs := Ptrofs.repr index).
  - apply pointer_location_value; eapply binary_expression_value with (v := Vptr object Ptrofs.zero) (w := Vint (Int.repr index)).
    + apply old_expression_value, value_temp; exact BYTES.
    + apply old_expression_value, value_int.
    + change (Some (Vptr object (Ptrofs.add Ptrofs.zero (Ptrofs.mul Ptrofs.one (Ptrofs.of_ints (Int.repr index))))) =
        Some (Vptr object (Ptrofs.repr index))).
      rewrite Ptrofs.add_zero_l, Ptrofs.mul_commut, Ptrofs.mul_one.
      unfold Ptrofs.of_ints; rewrite Int.signed_repr by
        (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia); reflexivity.
  - apply deref_loc_value with (chunk := Mint8signed); [reflexivity |exact LOAD].
Qed.
