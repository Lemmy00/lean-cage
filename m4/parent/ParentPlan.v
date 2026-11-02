(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanCageMainNumber Require Import NumberMath.
From LeanCagePlan Require Import PlanCodec.
From LeanCageParent Require Import ParentStructure ParentControl ParentDecision.
Import ListNotations.
Open Scope Z_scope.
Theorem parent_plan_parser bytes : option_map Z.of_nat(plan_parsed bytes)=decimal_number bytes.
Proof. exact(plan_parser_value bytes). Qed.
Theorem parent_plan_value bytes pid : plan_parsed bytes=Some pid<->decimal_number bytes=Some(Z.of_nat pid).
Proof. exact(plan_parser_some bytes pid). Qed.
Theorem parent_plan_decision bytes observed : parent_decision bytes observed=
 match plan_parsed bytes with
 |None=>true
 |Some pid=>(Z.of_nat pid=?0)||(2147483647<?Z.of_nat pid)||negb(Int.eq observed(Int.repr(Z.of_nat pid)))end.
Proof.
 unfold parent_decision;rewrite<-parent_plan_parser;destruct(plan_parsed bytes);reflexivity.
Qed.
Theorem parent_plan_acceptance bytes observed : parent_decision bytes observed=false<->
 exists pid,plan_parsed bytes=Some pid /\(0<Z.of_nat pid<=2147483647)%Z /\Int.signed observed=Z.of_nat pid.
Proof.
 rewrite parent_decision_exact;split.
 - intros[value[PARSED[RANGE MATCH]]];exists(Z.to_nat value);rewrite Z2Nat.id by lia.
   split;[apply parent_plan_value;rewrite Z2Nat.id by lia;exact PARSED|split;lia].
 - intros[pid[PARSED[RANGE MATCH]]];exists(Z.of_nat pid);split;[apply parent_plan_value;exact PARSED|split;lia].
Qed.
