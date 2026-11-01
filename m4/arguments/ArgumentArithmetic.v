(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Actual source, owned argument strings and explicit loss. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Ctypesdefs Cop.
Import ListNotations.
Open Scope Z_scope.
Fixpoint argument_bytes (sizes:list Z) := match sizes with []=>0|n::rest=>n+1+argument_bytes rest end.
Lemma argument_bytes_bound sizes : Forall(fun n=>1<=n<=4096)sizes ->
 0<=argument_bytes sizes<=4097*Z.of_nat(length sizes).
Proof. intros VALID;induction VALID;cbn[argument_bytes length];lia. Qed.
Lemma argument_bytes_no_wrap sizes : Forall(fun n=>1<=n<=4096)sizes ->
 Z.of_nat(length sizes)<=2147483647-16 -> argument_bytes sizes<=Int64.max_unsigned.
Proof. intros VALID COUNT;pose proof(argument_bytes_bound sizes VALID);
 change Int64.max_unsigned with 18446744073709551615;lia. Qed.
Lemma argument_total_add_exact ge m total n : 0<=total -> 1<=n<=4096 ->
 total+n+1<=Int64.max_unsigned ->
 sem_binary_operation ge Oadd(Vlong(Int64.repr total))tulong
 (Vlong(Int64.repr(n+1)))tulong m=Some(Vlong(Int64.repr(total+n+1))).
Proof.
 intros TOTAL SIZE BOUND;change(Some(Vlong(Int64.add(Int64.repr total)(Int64.repr(n+1))))=
 Some(Vlong(Int64.repr(total+n+1)))).
 unfold Int64.add;rewrite !Int64.unsigned_repr by lia;f_equal;f_equal;f_equal;lia.
Qed.
