(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
Require Import Machine Library ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationMemory ValidationValues.
Import ListNotations.
Open Scope nat_scope.
Lemma region_convert ge cell P R n start : region_certificate ge cell P R n start->
 forall Q S,(forall m,P m->Q m)->(forall s,R s->S s)->region_certificate ge cell Q S n start.
Proof.
 revert start;induction n as[|n IH];intros start CERT Q S MEMORY END;
 inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst.
 - constructor;auto.
 - constructor;auto.
 - eapply region_next;[auto|exact PROGRESS|].
   intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[[after[TARGET MEM]]|[next[TARGET[ADV TAIL]]]]];[left;exact WAIT| |].
   + right;left;exists after;auto.
   + right;right;exists next;split;[exact TARGET|];split;[exact ADV|];eapply IH;eauto.
Qed.
Ltac assembly_next := eapply region_source_prepend;[| |].
Lemma comparison_general cell P R remaining e le m k input output id size p bytes literal :
 P m->e!_strcmp=None->e!id=None->In id validation_literals->le!input=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address id)literal->
 (forall value,Int.eq value Int.zero=bytes_equal bytes literal->
 region_certificate main_ge cell P R remaining(State f_main Sskip k e(PTree.set output(Vint value)le)m))->
 region_certificate main_ge cell P R(3+remaining)(State f_main(comparison_call input output id size)k e le m).
Proof.
 intros GOOD GLOBAL LITERAL ID PTR OWN TEXT NEXT;cbn[Nat.add];unfold comparison_call.
 eapply region_source_prepend;[exact GOOD| |].
 - eapply certified_call_edge.
   + reflexivity.
   + apply old_expression_value;eapply value_function;
     [exact GLOBAL|exact(proj1 validation_function_bindings)|reflexivity].
   + eapply cons_argument_values;
     [apply old_expression_value;apply value_temp;exact PTR|reflexivity|].
     eapply cons_argument_values;
     [apply validation_literal_value;assumption|reflexivity|apply no_argument_values].
   + exact(proj1(proj2 validation_function_bindings)).
   + reflexivity.
 - eapply region_strcmp;[exact GOOD|exact OWN|exact TEXT|].
   intros value RESULT;eapply region_source_prepend;[exact GOOD|apply unchanged_store_edge;WriteAll.structural|].
   apply NEXT;eapply strcmp_exact_zero;eassumption.
Qed.
