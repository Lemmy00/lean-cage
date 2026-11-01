(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Readers.
From LeanCageController Require Import NumberMath.
Open Scope Z_scope.
Lemma number_byte_range b : 0<=Byte.unsigned b<=255.
Proof. pose proof (Byte.unsigned_range b);change (0<=Byte.unsigned b<256) in H;lia. Qed.
Lemma number_byte_unsigned b : Int.unsigned(byte_word b)=Byte.unsigned b.
Proof. unfold byte_word;apply Int.unsigned_repr;pose proof(number_byte_range b);change Int.max_unsigned with 4294967295;lia. Qed.
Lemma number_byte_signed b : Int.signed(byte_word b)=Byte.unsigned b.
Proof. unfold byte_word;apply Int.signed_repr;pose proof(number_byte_range b);change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia. Qed.
Lemma number_byte_zero b : byte_word b=Int.zero <-> b=Byte.zero.
Proof.
 split;[|intros ->;reflexivity]. intros E;apply(f_equal Int.unsigned) in E.
 rewrite number_byte_unsigned in E;change (Byte.unsigned b=0) in E.
 rewrite <- (Byte.repr_unsigned b),E;reflexivity.
Qed.
Lemma number_byte_narrow b : Int.zero_ext 8 (byte_word b)=byte_word b.
Proof.
 rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (byte_word b))).
 rewrite Int.zero_ext_mod by (change (0<=8<32);lia).
 rewrite number_byte_unsigned;change (Int.repr (Byte.unsigned b mod 256)=byte_word b).
 rewrite Z.mod_small;[reflexivity|pose proof(number_byte_range b);lia].
Qed.
Lemma number_signed_byte_zero b : Int.sign_ext 8 (byte_word b)=Int.zero <-> b=Byte.zero.
Proof.
 split;[|intros ->;reflexivity]. intros E.
 apply (f_equal (Int.zero_ext 8)) in E.
 rewrite Int.zero_ext_sign_ext in E by lia.
 rewrite number_byte_narrow in E. change (byte_word b=Int.zero) in E;now apply number_byte_zero in E.
Qed.
Definition number_machine_digit b := Int.sub (byte_word b) (Int.repr 48).
Definition number_machine_threshold b := Int64.divu
 (Int64.sub (Int64.repr (-1)) (Int64.repr(Int.signed(number_machine_digit b)))) (Int64.repr 10).
Definition number_machine_update acc b := Int64.add (Int64.mul (Int64.repr acc) (Int64.repr 10))
 (Int64.repr(Int.signed(number_machine_digit b))).
Lemma number_machine_digit_exact b : Int.signed(number_machine_digit b)=decimal_digit b.
Proof.
 unfold number_machine_digit;rewrite Int.sub_signed,number_byte_signed.
 change (Int.signed (Int.repr (Byte.unsigned b-48))=decimal_digit b).
 rewrite Int.signed_repr;[reflexivity|pose proof(number_byte_range b);
 change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia].
Qed.
Lemma number_machine_threshold_exact b : decimal_digit_ok b ->
 Int64.unsigned(number_machine_threshold b)=(decimal_max-decimal_digit b)/10.
Proof.
 intros DIG;unfold number_machine_threshold;rewrite number_machine_digit_exact.
 assert (D : 0<=decimal_digit b<=9) by (unfold decimal_digit,decimal_digit_ok in *;lia).
 unfold Int64.sub.
 change (Int64.unsigned (Int64.divu (Int64.repr (decimal_max-Int64.unsigned(Int64.repr(decimal_digit b)))) (Int64.repr 10))=(decimal_max-decimal_digit b)/10).
 rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615;lia).
 unfold Int64.divu.
 change (Int64.unsigned(Int64.repr(Int64.unsigned(Int64.repr(decimal_max-decimal_digit b))/10))=(decimal_max-decimal_digit b)/10).
 rewrite (Int64.unsigned_repr (decimal_max-decimal_digit b)) by (change Int64.max_unsigned with 18446744073709551615;unfold decimal_max;lia).
 apply Int64.unsigned_repr. change Int64.max_unsigned with decimal_max.
 split;[apply Z.div_pos;unfold decimal_max;lia|].
 apply Z.div_le_upper_bound;[lia|unfold decimal_max;lia].
Qed.
Lemma number_machine_update_exact acc b next :
 0<=acc -> decimal_step acc b=Some next -> number_machine_update acc b=Int64.repr next.
Proof.
 intros ACC STEP;apply decimal_step_exact in STEP;destruct STEP as [DIG [LIMIT NEXT]];subst next.
 assert (D : 0<=decimal_digit b<=9) by (unfold decimal_digit,decimal_digit_ok in *;lia).
 unfold number_machine_update;rewrite number_machine_digit_exact.
 unfold Int64.mul,Int64.add.
 change (Int64.repr
   (Int64.unsigned (Int64.repr (Int64.unsigned (Int64.repr acc)*10))
    + Int64.unsigned (Int64.repr (decimal_digit b)))
   = Int64.repr (acc*10+decimal_digit b)).
 rewrite (Int64.unsigned_repr acc) by (change Int64.max_unsigned with decimal_max;unfold decimal_max in *;lia).
 rewrite (Int64.unsigned_repr (acc*10)) by (change Int64.max_unsigned with decimal_max;unfold decimal_max in *;lia).
 rewrite (Int64.unsigned_repr (decimal_digit b)) by (change Int64.max_unsigned with decimal_max;unfold decimal_max in *;lia).
 reflexivity.
Qed.
Lemma number_low_test b : Int.lt (byte_word b) (Int.repr 48) = (Byte.unsigned b <? 48).
Proof.
 unfold Int.lt;rewrite number_byte_signed;change ((if zlt (Byte.unsigned b) 48 then true else false)=(Byte.unsigned b <? 48)).
 destruct (zlt (Byte.unsigned b) 48);symmetry;[apply Z.ltb_lt|apply Z.ltb_ge];lia.
Qed.
Lemma number_high_test b : Int.lt (Int.repr 57) (byte_word b) = (57 <? Byte.unsigned b).
Proof.
 unfold Int.lt;rewrite number_byte_signed;change ((if zlt 57 (Byte.unsigned b) then true else false)=(57 <? Byte.unsigned b)).
 destruct (zlt 57 (Byte.unsigned b));symmetry;[apply Z.ltb_lt|apply Z.ltb_ge];lia.
Qed.
Lemma number_overflow_test_exact acc b : 0<=acc<=decimal_max -> decimal_digit_ok b ->
 Int64.ltu (number_machine_threshold b) (Int64.repr acc) = negb (acc <=? (decimal_max-decimal_digit b)/10).
Proof.
 intros ACC DIG;unfold Int64.ltu;rewrite number_machine_threshold_exact by exact DIG.
 rewrite Int64.unsigned_repr by (change Int64.max_unsigned with decimal_max;exact ACC).
 destruct(zlt ((decimal_max-decimal_digit b)/10) acc).
 - rewrite (proj2 (Z.leb_gt acc ((decimal_max-decimal_digit b)/10)) ltac:(lia));reflexivity.
 - rewrite (proj2 (Z.leb_le acc ((decimal_max-decimal_digit b)/10)) ltac:(lia));reflexivity.
Qed.
Lemma number_nonzero_test b : b<>Byte.zero -> Int.eq (byte_word b) Int.zero=false.
Proof. intros NE;apply Int.eq_false;intros E;apply number_byte_zero in E;contradiction. Qed.
Lemma number_signed_nonzero_test b : b<>Byte.zero -> Int.eq (Int.sign_ext 8 (byte_word b)) Int.zero=false.
Proof. intros NE;apply Int.eq_false;intros E;apply number_signed_byte_zero in E;contradiction. Qed.
