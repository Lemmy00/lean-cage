(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanCageMainNumber Require Import NumberMath.
From LeanCageParent Require Import ParentStructure ParentWords ParentControl.
Open Scope Z_scope.
Definition parent_decision bytes observed :=
 parent_guard_bad(decimal_number bytes)||negb(Int.eq observed(Int.repr(parent_value(decimal_number bytes)))).
Theorem parent_decision_exact bytes observed : parent_decision bytes observed=false<->
 exists value,decimal_number bytes=Some value /\0<value<=2147483647 /\Int.signed observed=value.
Proof.
 unfold parent_decision;destruct(decimal_number bytes)as[value|]eqn:PARSED.
 - pose proof(proj1(decimal_number_exact bytes value)PARSED)as[NE[DIG[FOLD RANGE]]].
   unfold parent_guard_bad,parent_value;rewrite !Bool.orb_false_iff,Bool.negb_false_iff,Z.eqb_neq,Z.ltb_ge.
   split.
   + intros[[NONZERO UPPER]EQ];exists value;split;[reflexivity|];split;[lia|].
     apply(proj1(parent_match_signed value observed ltac:(lia)));exact EQ.
   + intros[found[SAME[VALID EQ]]];injection SAME as SAME;subst found;split;[split;lia|].
     apply(proj2(parent_match_signed value observed VALID));exact EQ.
 - cbn[parent_guard_bad];split;[discriminate|intros[value[SAME _]];discriminate].
Qed.
Theorem parent_invalid_never_matches bytes :
 (decimal_number bytes=None \/decimal_number bytes=Some 0 \/
  exists value,decimal_number bytes=Some value /\2147483647<value)->
 forall observed,parent_decision bytes observed=true.
Proof.
 intros INVALID observed;destruct(parent_decision bytes observed)eqn:DECISION;[reflexivity|].
 apply parent_decision_exact in DECISION;destruct DECISION as[value[PARSED[RANGE MATCH]]].
 destruct INVALID as[INVALID|[INVALID|[bad[INVALID LARGE]]]].
 - congruence.
 - assert(value=0)by congruence;lia.
 - assert(value=bad)by congruence;lia.
Qed.
Theorem parent_negative_observation_rejects bytes observed : Int.signed observed<=0->parent_decision bytes observed=true.
Proof.
 intros LOW;destruct(parent_decision bytes observed)eqn:DECISION;[reflexivity|].
 apply parent_decision_exact in DECISION;destruct DECISION as[value[PARSED[RANGE MATCH]]];lia.
Qed.
