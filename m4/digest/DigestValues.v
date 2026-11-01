(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Typed pointer, signed-character and boolean evaluations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Readers Library ClightSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageDigest Require Import DigestWords DigestMemory.
Open Scope Z_scope.
Definition digest_read := Ederef(Ebinop Oadd(Etempvar _s(tptr tschar))
 (Etempvar _i tuint)(tptr tschar))tschar.
Definition digest_registers le p i := le!_s=Some(address_value p) /\ le!_i=Some(Vint(Int.repr i)).
Lemma digest_pointer_expression e le m p i : digest_registers le p i->0<=i<=64->
 expression_value main_ge e le m
 (Ebinop Oadd(Etempvar _s(tptr tschar))(Etempvar _i tuint)(tptr tschar))
 (Vptr(address_block p)(Ptrofs.add(Ptrofs.repr(address_offset p))(Ptrofs.repr i))).
Proof.
 intros[PTR INDEX]RANGE;eapply binary_expression_value.
 - apply old_expression_value;apply value_temp;exact PTR.
 - apply old_expression_value;apply value_temp;exact INDEX.
 - apply digest_pointer_add;exact RANGE.
Qed.
Lemma digest_read_expression e le m p i b : digest_registers le p i->0<=i<=64->
 Mem.loadv Mint8signed m(Vptr(address_block p)(Ptrofs.add(Ptrofs.repr(address_offset p))(Ptrofs.repr i)))=
 Some(Vint(Int.sign_ext 8(byte_word b)))->
 expression_value main_ge e le m digest_read(Vint(Int.sign_ext 8(byte_word b))).
Proof.
 intros REGS RANGE LOAD;eapply location_read_value.
 - apply pointer_location_value;eapply digest_pointer_expression;eassumption.
 - eapply deref_loc_value;[reflexivity|exact LOAD].
Qed.
Lemma digest_lower_expression e le m id b bound :
 le!id=Some(Vint(Int.sign_ext 8(byte_word b)))->0<=bound<=127->
 expression_value main_ge e le m(Ebinop Oge(Etempvar id tschar)(Econst_int(Int.repr bound)tint)tint)
 (Val.of_bool(bound<=?digest_signed b)).
Proof.
 intros REG RANGE;eapply binary_expression_value;
 [apply old_expression_value;apply value_temp;exact REG|
 apply old_expression_value;apply value_int|apply digest_character_lower;exact RANGE].
Qed.
Lemma digest_upper_expression e le m id b bound :
 le!id=Some(Vint(Int.sign_ext 8(byte_word b)))->0<=bound<=127->
 expression_value main_ge e le m
 (Ecast(Ebinop Ole(Etempvar id tschar)(Econst_int(Int.repr bound)tint)tint)tbool)
 (Val.of_bool(digest_signed b<=?bound)).
Proof.
 intros REG RANGE;eapply cast_expression_value.
 - eapply binary_expression_value;
   [apply old_expression_value;apply value_temp;exact REG|
    apply old_expression_value;apply value_int|apply digest_character_upper;exact RANGE].
 - apply number_bool_cast.
Qed.
Lemma digest_test_expression e le m i : le!_i=Some(Vint(Int.repr i))->0<=i<=64->
 expression_value main_ge e le m(Ebinop Olt(Etempvar _i tuint)(Econst_int(Int.repr 64)tint)tint)
 (Val.of_bool(i<?64)).
Proof.
 intros REG RANGE;eapply binary_expression_value;
 [apply old_expression_value;apply value_temp;exact REG|
 apply old_expression_value;apply value_int|apply digest_index_test;exact RANGE].
Qed.
Lemma digest_length_expression e le m n :
 le!_t'1=Some(Vlong(Int64.repr n))->0<=n<=Int64.max_unsigned->
 expression_value main_ge e le m
 (Ebinop One(Etempvar _t'1 tulong)(Econst_int(Int.repr 64)tint)tint)
 (Val.of_bool(negb(n=?64))).
Proof.
 intros REG RANGE;eapply binary_expression_value;
 [apply old_expression_value;apply value_temp;exact REG|apply old_expression_value;apply value_int|].
 change(Some(Val.of_bool(negb(Int64.eq(Int64.repr n)(Int64.repr 64))))=
 Some(Val.of_bool(negb(n=?64)))).
 unfold Int64.eq;rewrite Int64.unsigned_repr by exact RANGE.
 change(Int64.unsigned(Int64.repr 64))with 64.
 destruct(zeq n 64);destruct(n=?64)eqn:EQ;try reflexivity;
 apply Z.eqb_eq in EQ||apply Z.eqb_neq in EQ;congruence.
Qed.
