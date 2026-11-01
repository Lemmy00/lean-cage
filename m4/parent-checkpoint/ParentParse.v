(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine Library ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberStructure NumberStorage NumberMemory NumberSource.
From LeanCageMain Require Import Main MainStructure MainValues.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentStructure.
Import ListNotations.
Open Scope nat_scope.
Definition parent_loaded le p := PTree.set _t'291(address_value p)le.
Definition parent_number_cont e le k := Kcall(Some _t'11)f_main e le(parent_parse_cont k).
Ltac parent_parse_next := eapply store_next;[reflexivity| |].
Ltac parent_parse_route := parent_parse_next;[apply unchanged_store_edge;WriteAll.structural|].
Lemma parent_to_number e le m k argv ofs p output :
 e!_number=None->e!_parent=Some(output,tulong)->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p)->
 store_path main_ge(fun after=>after=m)(State f_main(validation_suffix 15)k e le m)9
 (number_initial(address_value p)(Vptr output Ptrofs.zero)(parent_number_cont e(parent_loaded le p)k)m).
Proof.
 intros NUMBER LOCAL ARGV LOAD.
 change(validation_suffix 15)with(Ssequence(selection_check 15)(selection_after 15));parent_parse_route.
 rewrite(proj1 parent_source_structure);parent_parse_route.
 unfold parent_conditions;parent_parse_route;parent_parse_route;parent_parse_route.
 unfold parent_parse;parent_parse_route;parent_parse_next.
 - apply certified_set_edge;eapply validation_argv_value;[exact ARGV|lia|exact LOAD].
 - parent_parse_route;parent_parse_next.
   + eapply certified_call_edge.
     * reflexivity.
     * apply old_expression_value;eapply value_function;[exact NUMBER|exact(proj1 main_number_binding)|reflexivity].
     * eapply cons_argument_values;[apply old_expression_value;apply value_temp;apply PTree.gss|reflexivity|].
       eapply cons_argument_values.
       -- apply main_address_value;apply local_location_value;exact LOCAL.
       -- reflexivity.
       -- apply no_argument_values.
     * exact(proj2 main_number_binding).
     * reflexivity.
   + constructor;reflexivity.
Qed.
Lemma parent_loaded_frame le p : validation_frame le(parent_loaded le p).
Proof. unfold validation_frame,parent_loaded;split;WriteAll.lookup. Qed.
Lemma parent_parsed_frame le parsed : validation_frame le(PTree.set _t'11(number_code parsed)le).
Proof. unfold validation_frame;split;WriteAll.lookup. Qed.
