(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Library LibraryMachine Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageDigest Require Import DigestStructure DigestWords DigestSource.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationMemory ValidationValues.
Import ListNotations.
Open Scope nat_scope.
Ltac validation_next := eapply region_source_prepend;[reflexivity| |].
Ltac validation_route := validation_next;[apply unchanged_store_edge;WriteAll.structural|].
Lemma comparison_call_certificate cell R remaining e le m k input output id size p bytes literal :
 e!_strcmp=None->e!id=None->In id validation_literals->le!input=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address id)literal->
 (forall value,Int.eq value Int.zero=bytes_equal bytes literal->
 region_certificate main_ge cell(fun after=>after=m)R remaining
 (State f_main Sskip k e(PTree.set output(Vint value)le)m))->
 region_certificate main_ge cell(fun after=>after=m)R(3+remaining)
 (State f_main(comparison_call input output id size)k e le m).
Proof.
 intros GLOBAL LITERAL ID PTR OWN TEXT NEXT;cbn[Nat.add];unfold comparison_call.
 validation_next.
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
 - eapply region_strcmp;[reflexivity|exact OWN|exact TEXT|].
   intros value RESULT;validation_route;apply NEXT;eapply strcmp_exact_zero;eassumption.
Qed.
Lemma digest_invocation_certificate cell R remaining e le m k input output p bytes :
 e!_digest_text=None->le!input=Some(address_value p)->c_string m p bytes->
 region_certificate main_ge cell(fun after=>after=m)R remaining
 (State f_main Sskip k e(PTree.set output(Val.of_bool(digest_valid bytes))le)m)->
 region_certificate main_ge cell(fun after=>after=m)R(2070+remaining)
 (State f_main(Scall(Some output)(Evar _digest_text digest_type)[Etempvar input(tptr tschar)])k e le m).
Proof.
 intros GLOBAL PTR OWN NEXT.
 destruct(digest_source cell m p bytes(Kcall(Some output)f_main e le k)OWN)as[count[BOUND PATH]].
 apply region_weaken with(n:=S(count+S remaining));[|lia].
 validation_next.
 - eapply certified_call_edge.
   + reflexivity.
   + apply old_expression_value;eapply value_function;
     [exact GLOBAL|exact(proj1(proj2(proj2 validation_function_bindings)))|reflexivity].
   + eapply cons_argument_values;
     [apply old_expression_value;apply value_temp;exact PTR|reflexivity|apply no_argument_values].
   + exact(proj2(proj2(proj2 validation_function_bindings))).
   + reflexivity.
 - eapply region_string_path;[exact PATH|reflexivity|];cbn[call_cont].
   validation_route;exact NEXT.
Qed.
