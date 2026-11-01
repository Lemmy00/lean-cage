(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Signed indices, pointer arithmetic and unsigned lengths. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Library LocalAccess.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageBounds Require Import BoundsStructure BoundsWords.
From LeanCageArguments Require Import ArgumentArithmetic.
Import ListNotations.
Open Scope Z_scope.
Definition argument_bad n := (n=?0)||(4096<?n).
Lemma argument_bad_false n : 0<=n -> argument_bad n=false <-> 1<=n<=4096.
Proof.
 intros N;unfold argument_bad;rewrite Bool.orb_false_iff,Z.eqb_neq,Z.ltb_ge;lia.
Qed.
Lemma argument_strlen_range m p bytes : c_string m p bytes ->
 0<=Z.of_nat(length bytes)<Int64.max_unsigned.
Proof.
 intros [_[[OFFSET[SPAN SIZE]]LOAD]];rewrite length_app in SIZE;change(Z.of_nat(length bytes+1)<=Int64.max_unsigned)in SIZE;rewrite Nat2Z.inj_add in SIZE;lia.
Qed.
Lemma argument_index_test ge m i argc : 0<=i<=argc -> argc<=2147483647 ->
 sem_binary_operation ge Olt(Vint(Int.repr i))tint(Vint(Int.repr argc))tint m=
 Some(Val.of_bool(i<?argc)).
Proof.
 intros INDEX ARGC;change(Some(Val.of_bool(Int.lt(Int.repr i)(Int.repr argc))))with
 (Some(Val.of_bool(Int.lt(Int.repr i)(Int.repr argc)))).
 change(Some(Val.of_bool(Int.lt(Int.repr i)(Int.repr argc)))=Some(Val.of_bool(i<?argc))).
 unfold Int.lt;rewrite !Int.signed_repr by(change Int.min_signed with(-2147483648);change Int.max_signed with 2147483647;lia).
 f_equal;f_equal;destruct(zlt i argc);symmetry;[apply Z.ltb_lt|apply Z.ltb_ge];lia.
Qed.
Lemma argument_index_add ge m i : 0<=i<2147483647 ->
 sem_binary_operation ge Oadd(Vint(Int.repr i))tint(Vint(Int.repr 1))tint m=
 Some(Vint(Int.repr(i+1))).
Proof.
 intros INDEX;change(Some(Vint(Int.add(Int.repr i)(Int.repr 1)))=Some(Vint(Int.repr(i+1)))).
 rewrite Int.add_signed;rewrite Int.signed_repr by(change(-2147483648<=i<=2147483647);lia);reflexivity.
Qed.
Lemma argument_pointer_add ge m block offset i : 0<=i<=2147483647 ->
 sem_binary_operation ge Oadd(Vptr block offset)(tptr(tptr tschar))(Vint(Int.repr i))tint m=
 Some(Vptr block(Ptrofs.add offset(Ptrofs.repr(8*i)))).
Proof.
 intros INDEX;change(Some(Vptr block(Ptrofs.add offset(Ptrofs.mul(Ptrofs.repr 8)
  (Ptrofs.of_ints(Int.repr i)))))=Some(Vptr block(Ptrofs.add offset(Ptrofs.repr(8*i))))).
 unfold Ptrofs.of_ints;rewrite Int.signed_repr by(change(-2147483648<=i<=2147483647);lia).
 rewrite Ptrofs.mul_signed;rewrite !Ptrofs.signed_repr by
 (change Ptrofs.min_signed with(-9223372036854775808);change Ptrofs.max_signed with 9223372036854775807;lia).
 reflexivity.
Qed.
Lemma argument_empty_value m n : 0<=n<=Int64.max_unsigned ->
 sem_unary_operation Onotbool(Vlong(Int64.repr n))tulong m=Some(Val.of_bool(n=?0)).
Proof.
 intros N;change(Some(Val.of_bool(negb(negb(Int64.eq(Int64.repr n)Int64.zero))))=
 Some(Val.of_bool(n=?0))).
 rewrite bounds_long_zero by exact N;destruct(n=?0);reflexivity.
Qed.
Lemma argument_size_value ge m n : 0<=n<=Int64.max_unsigned ->
 sem_binary_operation ge Ogt(Vlong(Int64.repr n))tulong(Vint(Int.repr 4096))tint m=
 Some(Val.of_bool(4096<?n)).
Proof. intros N;exact(bounds_narrow_operation ge m upper n 4096 N ltac:(lia)). Qed.
Lemma argument_size_plus_nul ge m n : 1<=n<=4096 ->
 sem_binary_operation ge Oadd(Vlong(Int64.repr n))tulong(Vint(Int.repr 1))tint m=
 Some(Vlong(Int64.repr(n+1))).
Proof.
 intros N;change(Some(Vlong(Int64.add(Int64.repr n)(Int64.repr 1)))=Some(Vlong(Int64.repr(n+1)))).
 unfold Int64.add;rewrite Int64.unsigned_repr by(change(0<=n<=18446744073709551615);lia);reflexivity.
Qed.
Lemma argument_accumulator_range i n total : 16<=i<2147483647 ->
 0<=total<=4097*(i-16) -> 1<=n<=4096 ->
 0<=total+n+1<=4097*((i+1)-16) /\ total+n+1<=Int64.max_unsigned.
Proof. intros INDEX TOTAL N;change Int64.max_unsigned with 18446744073709551615;lia. Qed.
