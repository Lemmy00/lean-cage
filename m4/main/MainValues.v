(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Typed local-array, argument-pointer and machine-index evaluation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps LocalAccess CallAccess WriteAll.
From LeanCageMain Require Import Main MainStructure MainMemory.
Import ListNotations.
Open Scope Z_scope.
Definition numeric_registers le argv ofs i :=
 le ! _argv=Some(Vptr argv ofs) /\ le ! _i=Some(Vint(Int.repr i)).
Definition numeric_locals (e : env) fields := e ! _fields=Some(fields,tarray(tptr tulong)10) /\ e ! _number=None.
Lemma main_array_value ge e le m fields : e ! _fields=Some(fields,tarray(tptr tulong)10) ->
 expression_value ge e le m(Evar _fields(tarray(tptr tulong)10))(Vptr fields Ptrofs.zero).
Proof.
 intros LOCAL;eapply location_read_value;[apply local_location_value;exact LOCAL|].
 apply deref_loc_reference;reflexivity.
Qed.
Lemma main_pointer_add_unsigned ge m b ofs ty i : 0<=i<=12 ->
 sem_binary_operation ge Oadd (Vptr b ofs)(tptr(tptr ty))(Vint(Int.repr i))tuint m=
 Some(Vptr b(Ptrofs.add ofs(Ptrofs.repr(8*i)))).
Proof.
 intros INDEX;change (Some(Vptr b(Ptrofs.add ofs(Ptrofs.mul(Ptrofs.repr 8)
  (Ptrofs.of_intu(Int.repr i)))))=Some(Vptr b(Ptrofs.add ofs(Ptrofs.repr(8*i))))).
 unfold Ptrofs.of_intu,Ptrofs.of_int;rewrite Int.unsigned_repr by (change (0<=i<=4294967295);lia).
 rewrite Ptrofs.mul_signed;rewrite !Ptrofs.signed_repr by (change Ptrofs.min_signed with (-9223372036854775808);change Ptrofs.max_signed with 9223372036854775807;lia).
 reflexivity.
Qed.
Lemma main_index_add ge m i n : 0<=i<=10 -> 0<=n<=2 ->
 sem_binary_operation ge Oadd(Vint(Int.repr i))tuint(Vint(Int.repr n))tint m=Some(Vint(Int.repr(i+n))).
Proof.
 intros INDEX N;change (Some(Vint(Int.add(Int.repr i)(Int.repr n)))=Some(Vint(Int.repr(i+n)))).
 unfold Int.add;rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity.
Qed.
Lemma main_index_test ge m i : 0<=i<=10 ->
 sem_binary_operation ge Olt(Vint(Int.repr i))tuint(Vint(Int.repr 10))tint m=
 Some(Val.of_bool(i<?10)).
Proof.
 intros INDEX;change (Some(Val.of_bool(Int.ltu(Int.repr i)(Int.repr 10)))=Some(Val.of_bool(i<?10))).
 unfold Int.ltu;rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia).
 destruct(zlt i 10);destruct(i<?10)eqn:E;try reflexivity;apply Z.ltb_lt in E||apply Z.ltb_ge in E;lia.
Qed.
Lemma main_field_pointer_value e le m fields i :
 e ! _fields=Some(fields,tarray(tptr tulong)10) -> le ! _i=Some(Vint(Int.repr i)) -> 0<=i<10 ->
 expression_value main_ge e le m
 (Ebinop Oadd(Evar _fields(tarray(tptr tulong)10))(Etempvar _i tuint)(tptr(tptr tulong)))
 (Vptr fields(Ptrofs.repr(8*i))).
Proof.
 intros LOCAL INDEX BOUND;eapply binary_expression_value.
 - apply main_array_value;exact LOCAL.
 - apply old_expression_value;apply value_temp;exact INDEX.
 - change (sem_binary_operation main_ge Oadd(Vptr fields Ptrofs.zero)(tptr(tptr tulong))
    (Vint(Int.repr i))tuint m=Some(Vptr fields(Ptrofs.repr(8*i)))).
   rewrite main_pointer_add_unsigned by lia;rewrite Ptrofs.add_zero_l;reflexivity.
Qed.
Lemma main_argument_pointer_value e le m argv ofs i : numeric_registers le argv ofs i -> 0<=i<10 ->
 expression_value main_ge e le m
 (Ebinop Oadd(Etempvar _argv(tptr(tptr tschar)))
  (Ebinop Oadd(Etempvar _i tuint)(Econst_int(Int.repr 2)tint)tuint)(tptr(tptr tschar)))
 (Vptr argv(argument_offset ofs i)).
Proof.
 intros [ARGV INDEX] BOUND;eapply binary_expression_value.
 - apply old_expression_value;apply value_temp;exact ARGV.
 - eapply binary_expression_value.
   + apply old_expression_value;apply value_temp;exact INDEX.
   + apply old_expression_value;apply value_int.
   + apply main_index_add;lia.
 - apply main_pointer_add_unsigned;lia.
Qed.
Lemma main_pointer_load ge e le m a ty b ofs value :
 expression_value ge e le m a(Vptr b ofs) -> Mem.loadv Mptr m(Vptr b ofs)=Some value ->
 expression_value ge e le m(Ederef a(tptr ty))value.
Proof.
 intros PTR LOAD;eapply location_read_value;[apply pointer_location_value;exact PTR|].
 eapply deref_loc_value;[reflexivity|exact LOAD].
Qed.
Lemma main_address_value ge e le m a ty b ofs :
 location_value ge e le m a b ofs -> expression_value ge e le m(Eaddrof a ty)(Vptr b ofs).
Proof.
 intros [REAL UNIQUE];split;[constructor;exact REAL|].
 intros other EV;inversion EV;subst.
 - match goal with LV : eval_lvalue _ _ _ _ a _ _ _ |- _=>
     destruct(UNIQUE _ _ _ LV)as[BL[OFF BF]];subst end;reflexivity.
 - match goal with LV : eval_lvalue _ _ _ _(Eaddrof _ _) _ _ _ |- _=>inversion LV end.
Qed.
