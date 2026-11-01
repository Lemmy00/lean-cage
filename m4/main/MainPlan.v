(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Imported byte-interface results drive the complete-helper block. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps ScalarMemory.
From LeanCageController Require Import NumberMath.
From LeanCagePlan Require Import PlanCodec PlanSource.
From LeanCageMainNumber Require Import NumberMath.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainLoop MainFields MainEntry MainSource MainOutcomes.
Import ListNotations.
Open Scope Z_scope.
Theorem full_helper_decimal_identity bytes :
 LeanCageMainNumber.NumberMath.decimal_number bytes=LeanCageController.NumberMath.decimal_number bytes.
Proof. reflexivity. Qed.
Fixpoint imported_field_values fields : list Z := match fields with
 | []=>[]|bytes::rest=>match plan_result bytes with Some v=>v::imported_field_values rest|None=>[]end end.
Fixpoint imported_fields_complete fields : bool := match fields with
 | []=>true|bytes::rest=>match plan_result bytes with Some _=>imported_fields_complete rest|None=>false end end.
Theorem imported_values_exact fields : imported_field_values fields=field_values fields.
Proof.
 induction fields as[|bytes rest IH];[reflexivity|].
 cbn[imported_field_values field_values];unfold plan_result;rewrite plan_parser_value,<-full_helper_decimal_identity.
 destruct(decimal_number bytes);[rewrite IH|];reflexivity.
Qed.
Theorem imported_completion_exact fields : imported_fields_complete fields=fields_complete fields.
Proof.
 induction fields as[|bytes rest IH];[reflexivity|].
 cbn[imported_fields_complete fields_complete];unfold plan_result;rewrite plan_parser_value,<-full_helper_decimal_identity.
 destruct(decimal_number bytes);auto.
Qed.
Theorem numeric_region_imported_source before fields argv ofs inputs e le k :
 length inputs=10%nat -> numeric_entry_buffers before fields argv ofs inputs ->
 numeric_locals e fields -> e!_policy__1=None -> le!_argv=Some(Vptr argv ofs) ->
 exists initialized count after final,
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(imported_field_values(map input_bytes inputs))after /\
 numeric_registers final argv ofs(Z.of_nat(length(imported_field_values(map input_bytes inputs)))) /\
 store_path main_ge(numeric_region_memory before initialized fields inputs)
 (State f_main numeric_region k e le before)count
 (if imported_fields_complete(map input_bytes inputs)
  then State f_main Sskip(Kseq after_numeric k)e final after
  else numeric_failure_state e final(Kseq after_numeric k)after).
Proof.
 rewrite imported_values_exact,imported_completion_exact,<-numeric_values_data,<-numeric_complete_data.
 apply numeric_region_source.
Qed.
