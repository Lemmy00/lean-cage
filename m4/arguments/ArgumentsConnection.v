(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: The imported acceptance and successful total select source outcomes. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
Require Import Machine.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath ArgumentStructure ArgumentMemory
 ArgumentSource ArgumentsImported.
Import ListNotations.
Open Scope Z_scope.
Lemma sizes_accept_owned inputs : sizes_accept(map guest_size inputs)=true <-> guest_sizes_valid inputs.
Proof.
 induction inputs as[|x rest IH];cbn[sizes_accept map].
 - split;[intros;constructor|intros;reflexivity].
 - rewrite !andb_true_iff,negb_true_iff,Z.eqb_neq,Z.leb_le,IH.
   split.
   + intros[[NONZERO HIGH]REST];constructor;[pose proof(guest_size_nonnegative x);lia|exact REST].
   + intros VALID;inversion VALID;subst;split;[split;lia|assumption].
Qed.
Lemma sizes_total_owned inputs : sizes_total(map guest_size inputs)=guest_total inputs.
Proof. induction inputs;cbn[sizes_total guest_total map];congruence. Qed.
Theorem imported_source_acceptance sizes inputs : argument_values sizes=map guest_size inputs ->
 imported_lengths_accept sizes=true <-> exists total,argument_scan 16 0 inputs=arguments_accepted total.
Proof.
 intros VALUES;rewrite(proj1(imported_argument_profile sizes)),VALUES,sizes_accept_owned.
 symmetry;apply argument_scan_accepts.
Qed.
Theorem imported_source_total sizes inputs : argument_values sizes=map guest_size inputs ->
 imported_lengths_accept sizes=true ->
 argument_scan 16 0 inputs=arguments_accepted(imported_lengths_total sizes).
Proof.
 intros VALUES GOOD;pose proof(proj1(imported_source_acceptance sizes inputs VALUES)GOOD)as ACCEPTED.
 apply argument_scan_accepts in ACCEPTED;rewrite(argument_scan_valid 16 0 inputs ACCEPTED).
 rewrite(proj2(imported_argument_profile sizes)),VALUES,sizes_total_owned;reflexivity.
Qed.
Theorem imported_source_rejection sizes inputs : argument_values sizes=map guest_size inputs ->
 imported_lengths_accept sizes=false ->
 exists index total,argument_scan 16 0 inputs=arguments_rejected index total.
Proof.
 intros VALUES BAD;destruct(argument_scan 16 0 inputs)as[total|index total]eqn:RESULT;[|eauto].
 assert(GOOD:imported_lengths_accept sizes=true).
 { apply(imported_source_acceptance sizes inputs VALUES);eauto. }
 congruence.
Qed.
Theorem imported_argument_source cell m argv ofs argc inputs sizes e le k :
 argument_values sizes=map guest_size inputs ->
 17<=argc<=2147483647 -> 16+Z.of_nat(length inputs)=argc -> guest_table_span ofs argc ->
 guest_arguments_owned m argv ofs 16 inputs -> e!_strlen=None ->
 le!_argv=Some(Vptr argv ofs) -> le!_argc=Some(Vint(Int.repr argc)) ->
 exists count final,(count<=26*length inputs+13)%nat /\
 string_path main_ge cell(State f_main argument_suffix k e le m)count
 (argument_endpoint(argument_scan 16 0 inputs)e final k m) /\
 (imported_lengths_accept sizes=true ->
  argument_scan 16 0 inputs=arguments_accepted(imported_lengths_total sizes)) /\
 (imported_lengths_accept sizes=false ->
  exists index total,argument_scan 16 0 inputs=arguments_rejected index total).
Proof.
 intros VALUES COUNT SIZE SPAN OWN GLOBAL ARGV ARGC.
 destruct(argument_region_source cell m argv ofs argc inputs e le k COUNT SIZE SPAN OWN GLOBAL ARGV ARGC)
 as[n[final[BOUND[REG PATH]]]]. exists n,final;split;[exact BOUND|];split;[exact PATH|];split.
 - apply imported_source_total;exact VALUES.
 - apply imported_source_rejection;exact VALUES.
Qed.
