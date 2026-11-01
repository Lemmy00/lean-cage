(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Compose actual accumulation and subsequent policy checks. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
Require Import Machine ClightSteps StoreSteps WriteAll.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsStructure BoundsMemory BoundsSequence BoundsSource.
From LeanCageArguments Require Import StringMachine StringPath ArgumentStructure ArgumentWords
 ArgumentValues ArgumentControl ArgumentMemory ArgumentSource.
Import ListNotations.
Open Scope Z_scope.
Definition argument_bounds_endpoint argc inputs values e le k m :=
 match argument_scan 16 0 inputs with
 |arguments_rejected _ _=>argument_failure_state e le(Kseq after_arguments k)m
 |arguments_accepted total=>bounds_endpoint e le(Kseq after_bounds k)m(bounds_rejected argc total values)
 end.
Theorem argument_bounds_source cell m argv ofs argc inputs values e le k :
 17<=argc<=2147483647 -> 16+Z.of_nat(length inputs)=argc -> guest_table_span ofs argc ->
 guest_arguments_owned m argv ofs 16 inputs -> e!_strlen=None -> e!_policy__1=None -> policy_image m values ->
 le!_argv=Some(Vptr argv ofs) -> le!_argc=Some(Vint(Int.repr argc)) ->
 exists count final,(count<=26*length inputs+154)%nat /\
 string_path main_ge cell(State f_main argument_suffix k e le m)count
 (argument_bounds_endpoint argc inputs values e final k m).
Proof.
 intros COUNT SIZE SPAN OWN GLOBAL POLICY IMAGE ARGV ARGC.
 destruct(argument_region_source cell m argv ofs argc inputs e le k COUNT SIZE SPAN OWN GLOBAL ARGV ARGC)
 as[n[intermediate[BOUND[REG PATH]]]].
 pose proof(argument_scan_range 16 0 argc inputs ltac:(lia)SIZE ltac:(lia))as RANGE.
 unfold argument_bounds_endpoint;destruct(argument_scan 16 0 inputs)as[total|index total]eqn:RESULT.
 - cbn[outcome_total]in RANGE;cbn[outcome_total outcome_index]in REG.
   assert(TOTAL:0<=total<=Int64.max_unsigned)by(change Int64.max_unsigned with 18446744073709551615;lia).
   destruct(bounds_region_source e intermediate m argc total values COUNT TOTAL
    (proj1(proj2 REG))(proj2(proj2(proj2 REG)))POLICY IMAGE)as[boundcount[final[LIMIT BOUNDS]]].
   exists(n+1+boundcount)%nat,final;split;[lia|].
   replace(n+1+boundcount)%nat with(n+S boundcount)%nat by lia.
   eapply string_path_trans with(n:=n);[exact PATH|].
   change after_arguments with(Ssequence bounds_region after_bounds).
   eapply string_next;[apply string_source_edge;WriteAll.structural|].
   apply string_store_path with(m:=m);apply BOUNDS.
 - exists n,intermediate;split;[lia|exact PATH].
Qed.
