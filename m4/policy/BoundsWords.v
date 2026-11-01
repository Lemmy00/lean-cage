(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Exact mixed-width comparisons, subtraction and modulus. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import LocalAccess.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageBounds Require Import BoundsStructure.
Open Scope Z_scope.
Lemma bounds_ltu x y : 0<=x<=Int64.max_unsigned -> 0<=y<=Int64.max_unsigned ->
 Int64.ltu(Int64.repr x)(Int64.repr y)=(x<?y).
Proof.
 intros X Y;unfold Int64.ltu;rewrite !Int64.unsigned_repr by assumption.
 destruct(zlt x y);symmetry;[apply Z.ltb_lt|apply Z.ltb_ge];lia.
Qed.
Lemma bounds_long_zero x : 0<=x<=Int64.max_unsigned -> Int64.eq(Int64.repr x)Int64.zero=(x=?0).
Proof.
 intros X;unfold Int64.eq;rewrite Int64.unsigned_repr by exact X;change(Int64.unsigned Int64.zero)with 0.
 destruct(zeq x 0);symmetry;[apply Z.eqb_eq|apply Z.eqb_neq];assumption.
Qed.
Definition bound_operation_value kind x bound := match kind with
 | lower=>Val.of_bool(x<?bound) | upper=>Val.of_bool(bound<?x)
 | aligned=>Vlong(Int64.repr(x mod bound))end.
Lemma bounds_machine_operation ge m kind x bound :
 0<=x<=Int64.max_unsigned -> 0<bound<=Int64.max_unsigned ->
 sem_binary_operation ge(match kind with lower=>Olt|upper=>Ogt|aligned=>Omod end)
 (Vlong(Int64.repr x))tulong(Vlong(Int64.repr bound))tulong m=
 Some(bound_operation_value kind x bound).
Proof.
 intros X B;destruct kind.
 - change (Some(Val.of_bool(Int64.ltu(Int64.repr x)(Int64.repr bound)))=Some(Val.of_bool(x<?bound))).
   rewrite bounds_ltu by lia;reflexivity.
 - change (Some(Val.of_bool(Int64.ltu(Int64.repr bound)(Int64.repr x)))=Some(Val.of_bool(bound<?x))).
   rewrite bounds_ltu by lia;reflexivity.
 - change((if Int64.eq(Int64.repr bound)Int64.zero then None else
    Some(Vlong(Int64.modu(Int64.repr x)(Int64.repr bound))))=Some(Vlong(Int64.repr(x mod bound)))).
   rewrite bounds_long_zero by lia;rewrite (proj2(Z.eqb_neq bound 0)ltac:(lia)).
   unfold Int64.modu;rewrite !Int64.unsigned_repr by lia;reflexivity.
Qed.
Lemma bounds_operation_cast m kind x bound :
 0<=x<=Int64.max_unsigned -> 0<bound<=Int64.max_unsigned ->
 sem_cast(bound_operation_value kind x bound)(match kind with aligned=>tulong|_=>tint end)tbool m=
 Some(Val.of_bool(match kind with lower=>x<?bound|upper=>bound<?x|aligned=>negb(x mod bound=?0)end)).
Proof.
 intros X B;destruct kind;[apply number_bool_cast|apply number_bool_cast|].
 change (Some(Vint(if Int64.eq(Int64.repr(x mod bound))Int64.zero then Int.zero else Int.one)) = Some(Val.of_bool(negb(x mod bound=?0)))).
 rewrite bounds_long_zero by(pose proof(Z.mod_pos_bound x bound ltac:(lia));lia).
 destruct(x mod bound=?0);reflexivity.
Qed.
Lemma bounds_narrow_operation ge m kind x bound :
 0<=x<=Int64.max_unsigned -> 0<bound<=2147483647 ->
 sem_binary_operation ge(match kind with lower=>Olt|upper=>Ogt|aligned=>Omod end)
 (Vlong(Int64.repr x))tulong(Vint(Int.repr bound))tint m=
 Some(bound_operation_value kind x bound).
Proof.
 intros X B.
 assert(SIGNED:Int.signed(Int.repr bound)=bound)by(apply Int.signed_repr;change(-2147483648<=bound<=2147483647);lia).
 replace (sem_binary_operation ge
  (match kind with lower=>Olt|upper=>Ogt|aligned=>Omod end)
  (Vlong(Int64.repr x))tulong(Vint(Int.repr bound))tint m)
 with (sem_binary_operation ge
  (match kind with lower=>Olt|upper=>Ogt|aligned=>Omod end)
  (Vlong(Int64.repr x))tulong(Vlong(Int64.repr(Int.signed(Int.repr bound))))tulong m)
 by (destruct kind;reflexivity).
 rewrite SIGNED;apply bounds_machine_operation;[exact X|change(0<bound<=18446744073709551615);lia].
Qed.

Lemma bounds_argc_sub ge m argc : 17<=argc<=2147483647 ->
 sem_binary_operation ge Osub(Vint(Int.repr argc))tint(Vint(Int.repr 16))tint m=
 Some(Vint(Int.repr(argc-16))).
Proof.
 intros RANGE;change(Some(Vint(Int.sub(Int.repr argc)(Int.repr 16))))with
 (Some(Vint(Int.sub(Int.repr argc)(Int.repr 16)))).
 change(Some(Vint(Int.sub(Int.repr argc)(Int.repr 16)))=Some(Vint(Int.repr(argc-16)))).
 rewrite Int.sub_signed;rewrite Int.signed_repr by(change(-2147483648<=argc<=2147483647);lia).
 reflexivity.
Qed.
Lemma bounds_argc_cmp ge m argc : 17<=argc<=2147483647 ->
 sem_binary_operation ge Ogt(Vint(Int.repr(argc-16)))tint(Vint(Int.repr 64))tint m=
 Some(Val.of_bool(64<?argc-16)).
Proof.
 intros RANGE;change(Some(Val.of_bool(Int.lt(Int.repr 64)(Int.repr(argc-16))))=
 Some(Val.of_bool(64<?argc-16))).
 unfold Int.lt;rewrite Int.signed_repr by(change(-2147483648<=64<=2147483647);lia).
 rewrite Int.signed_repr by(change(-2147483648<=argc-16<=2147483647);lia).
 f_equal;f_equal;destruct(zlt 64(argc-16));symmetry;[apply Z.ltb_lt|apply Z.ltb_ge];lia.
Qed.
