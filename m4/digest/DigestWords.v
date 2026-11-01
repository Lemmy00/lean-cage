(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Exact source digest syntax, reads and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Readers.
From LeanCageMainNumber Require Import NumberWords NumberControl.
Open Scope Z_scope.
Definition digest_hex (b:Byte.int) := ((48<=?Byte.unsigned b)&&(Byte.unsigned b<=?57))||
 ((97<=?Byte.unsigned b)&&(Byte.unsigned b<=?102)).
Lemma digest_signed_byte b : Int.signed(Int.sign_ext 8(byte_word b))=
 if zlt(Byte.unsigned b)128 then Byte.unsigned b else Byte.unsigned b-256.
Proof.
 pose proof(Int.sign_ext_range 8(byte_word b)ltac:(change(0<8<32);lia))as RANGE.
 pose proof(Int.eqmod_sign_ext 8(byte_word b)ltac:(change(0<8<32);lia))as[k EQ].
 change(-128<=Int.signed(Int.sign_ext 8(byte_word b))<128)in RANGE.
 rewrite number_byte_unsigned in EQ;change(two_p 8)with 256 in EQ.
 pose proof(number_byte_range b);destruct(zlt(Byte.unsigned b)128);lia.
Qed.
Definition digest_signed b := Int.signed(Int.sign_ext 8(byte_word b)).
Definition digest_digit b := (48<=?digest_signed b)&&(digest_signed b<=?57).
Definition digest_letter b := (97<=?digest_signed b)&&(digest_signed b<=?102).
Definition digest_valid bytes := (Z.of_nat(length bytes)=?64)&&forallb digest_hex bytes.
Lemma digest_index_test ge m i : 0<=i<=64 ->
 sem_binary_operation ge Olt(Vint(Int.repr i))tuint(Vint(Int.repr 64))tint m=
 Some(Val.of_bool(i<?64)).
Proof.
 intros RANGE;change(Some(Val.of_bool(Int.ltu(Int.repr i)(Int.repr 64)))=
 Some(Val.of_bool(i<?64))).
 unfold Int.ltu;rewrite Int.unsigned_repr by(change(0<=i<=4294967295);lia).
 change(Int.unsigned(Int.repr 64))with 64.
 f_equal;f_equal;destruct(zlt i 64);symmetry;[apply Z.ltb_lt|apply Z.ltb_ge];lia.
Qed.
Lemma digest_index_increment ge m i : 0<=i<64 ->
 sem_binary_operation ge Oadd(Vint(Int.repr i))tuint(Vint(Int.repr 1))tint m=
 Some(Vint(Int.repr(i+1))).
Proof.
 intros RANGE;change(Some(Vint(Int.add(Int.repr i)(Int.repr 1)))=
 Some(Vint(Int.repr(i+1)))).
 unfold Int.add;rewrite Int.unsigned_repr by(change(0<=i<=4294967295);lia);reflexivity.
Qed.
Lemma digest_pointer_add ge m b ofs i : 0<=i<=64 ->
 sem_binary_operation ge Oadd(Vptr b ofs)(tptr tschar)(Vint(Int.repr i))tuint m=
 Some(Vptr b(Ptrofs.add ofs(Ptrofs.repr i))).
Proof.
 intros RANGE;change(Some(Vptr b(Ptrofs.add ofs(Ptrofs.mul(Ptrofs.repr 1)
 (Ptrofs.of_intu(Int.repr i)))))=Some(Vptr b(Ptrofs.add ofs(Ptrofs.repr i)))).
 unfold Ptrofs.of_intu,Ptrofs.of_int;rewrite Int.unsigned_repr by(change(0<=i<=4294967295);lia).
 unfold Ptrofs.mul;rewrite !Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
 rewrite Z.mul_1_l;reflexivity.
Qed.
Lemma digest_signed_hex b :
 (((48<=?Int.signed(Int.sign_ext 8(byte_word b)))&&
   (Int.signed(Int.sign_ext 8(byte_word b))<=?57))||
  ((97<=?Int.signed(Int.sign_ext 8(byte_word b)))&&
   (Int.signed(Int.sign_ext 8(byte_word b))<=?102)))=digest_hex b.
Proof.
 unfold digest_hex;rewrite digest_signed_byte.
 destruct(zlt(Byte.unsigned b)128)as[LOW|HIGH];[reflexivity|].
 pose proof(number_byte_range b).
 repeat match goal with |-context[?a<=? ?c]=>destruct(a<=?c)eqn:E;
  [apply Z.leb_le in E|apply Z.leb_gt in E];try lia end;reflexivity.
Qed.
Lemma digest_character_lower ge m b bound : 0<=bound<=127 ->
 sem_binary_operation ge Oge(Vint(Int.sign_ext 8(byte_word b)))tschar(Vint(Int.repr bound))tint m=
 Some(Val.of_bool(bound<=?Int.signed(Int.sign_ext 8(byte_word b)))).
Proof.
 intros BOUND;change(Some(Val.of_bool(negb(Int.lt(Int.sign_ext 8(byte_word b))(Int.repr bound))))=
 Some(Val.of_bool(bound<=?Int.signed(Int.sign_ext 8(byte_word b))))).
 unfold Int.lt;rewrite Int.signed_repr by(change(-2147483648<=bound<=2147483647);lia).
 destruct(zlt(Int.signed(Int.sign_ext 8(byte_word b)))bound);cbn;
 destruct(bound<=?Int.signed(Int.sign_ext 8(byte_word b)))eqn:ORDER;try reflexivity;
 apply Z.leb_le in ORDER||apply Z.leb_gt in ORDER;lia.
Qed.
Lemma digest_character_upper ge m b bound : 0<=bound<=127 ->
 sem_binary_operation ge Ole(Vint(Int.sign_ext 8(byte_word b)))tschar(Vint(Int.repr bound))tint m=
 Some(Val.of_bool(Int.signed(Int.sign_ext 8(byte_word b))<=?bound)).
Proof.
 intros BOUND;change(Some(Val.of_bool(negb(Int.lt(Int.repr bound)(Int.sign_ext 8(byte_word b)))))=
 Some(Val.of_bool(Int.signed(Int.sign_ext 8(byte_word b))<=?bound))).
 unfold Int.lt;rewrite Int.signed_repr by(change(-2147483648<=bound<=2147483647);lia).
 destruct(zlt bound(Int.signed(Int.sign_ext 8(byte_word b))));cbn;
 destruct(Int.signed(Int.sign_ext 8(byte_word b))<=?bound)eqn:ORDER;try reflexivity;
 apply Z.leb_le in ORDER||apply Z.leb_gt in ORDER;lia.
Qed.
Lemma digest_hex_split b : digest_hex b=digest_digit b||digest_letter b.
Proof. symmetry;apply digest_signed_hex. Qed.
Theorem digest_hex_exact b : digest_hex b=true <->
 (48<=Byte.unsigned b<=57) \/ (97<=Byte.unsigned b<=102).
Proof. unfold digest_hex;rewrite orb_true_iff,!andb_true_iff,!Z.leb_le;tauto. Qed.
Theorem digest_high_byte_rejected b : 128<=Byte.unsigned b->digest_hex b=false.
Proof.
 intros HIGH;destruct(digest_hex b)eqn:HEX;[|reflexivity].
 apply digest_hex_exact in HEX;destruct HEX;lia.
Qed.
Theorem digest_valid_exact bytes : digest_valid bytes=true <->
 length bytes=64%nat /\ Forall(fun b=>(48<=Byte.unsigned b<=57)\/(97<=Byte.unsigned b<=102))bytes.
Proof.
 unfold digest_valid;rewrite andb_true_iff,Z.eqb_eq,forallb_forall,Forall_forall.
 split;intros[SIZE ALL];split;try lia;intros b IN;apply digest_hex_exact;apply ALL;exact IN.
Qed.
