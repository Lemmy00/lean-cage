(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Complete mathematical predicate of the actual ordered guards. *)
From Stdlib Require Import ZArith List Lia Bool.
From LeanCageBounds Require Import BoundsStructure.
Import ListNotations.
Open Scope Z_scope.
Definition numeric_limits values :=
 let memory:=nth 0 values 0 in let tasks:=nth 1 values 0 in let quota:=nth 2 values 0 in
 let cpu:=nth 3 values 0 in let wall:=nth 4 values 0 in let space:=nth 5 values 0 in
 let inodes:=nth 6 values 0 in let input:=nth 7 values 0 in let output:=nth 8 values 0 in
 let error:=nth 9 values 0 in
 ((16777216<=?memory)&&(memory<=?1073741824)&&(memory mod 4096=?0))&&
 ((4<=?tasks)&&(tasks<=?256))&&((1000<=?quota)&&(quota<=?100000))&&
 ((10000<=?cpu)&&(cpu<=?3600000000))&&((10<=?wall)&&(wall<=?3600000))&&
 ((1048576<=?space)&&(space<=?268435456)&&(space mod 4096=?0))&&
 ((64<=?inodes)&&(inodes<=?65536))&&(input<=?67108864)&&
 (output<=?16777216)&&(error<=?16777216).
Lemma bounds_not_less x y : negb(x<?y)=(y<=?x).
Proof.
 destruct(x<?y)eqn:LESS;cbn;symmetry;[apply Z.leb_gt;apply Z.ltb_lt in LESS|
 apply Z.leb_le;apply Z.ltb_ge in LESS];lia.
Qed.
Theorem numeric_limits_exact values : numeric_limits values=negb(policy_rejected values).
Proof.
 unfold numeric_limits,policy_rejected,policy_guards.
 cbn[existsb guard_bad guard_kind guard_bound guard_index Z.to_nat Pos.to_nat].
 rewrite !negb_orb,!bounds_not_less,!negb_involutive,!andb_true_r,!andb_assoc;reflexivity.
Qed.
Theorem bounds_predicate_exact argc bytes values :
 negb(bounds_rejected argc bytes values)=
 ((argc-16<=?64)&&(bytes<=?16384))&&numeric_limits values.
Proof.
 unfold bounds_rejected;rewrite !negb_orb,!bounds_not_less,<-numeric_limits_exact;reflexivity.
Qed.
