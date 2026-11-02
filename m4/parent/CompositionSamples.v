(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.cases: Complete-composition decisions and retained numeric store vectors. *)
From Stdlib Require Import ZArith List Lia Bool String.
From compcert Require Import Integers.
From LeanCageMain Require Import MainMemory MainOutcomes MainSamples.
From LeanCageArguments Require Import ArgumentSamples.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues.
From LeanCageInitialization Require Import InitializationWitnesses InitializationSamples.
From LeanCageParent Require Import ParentStructure ParentDecision ParentSamples.
Import ListNotations.
Open Scope Z_scope.

Inductive composition_kind := numeric_first(index:nat) | parent_first(observed:bool) |
 initialization_first(result:initialization_result).
Definition composition_kind_of fields parent observed export tree stdin guests :=
 if fields_complete fields then
 if parent_decision parent observed then parent_first(negb(parent_guard_bad(NumberMath.decimal_number parent)))
 else initialization_first(initialization_result_of export tree stdin guests(field_values fields))
 else numeric_first(List.length(field_values fields)).
Fixpoint decimal_digits fuel value : list byte := match fuel with
 |O=>[]|S fuel=>if value<?10 then[Byte.repr(48+value)]else decimal_digits fuel(value/10)++[Byte.repr(48+value mod 10)]end.
Record composition_case := {
 numeric_texts:list(list byte);parent_text:list byte;observed_parent:int;
 export_option:list byte;tree_option:list byte;stdin_option:list byte;guest_sources:list(list byte);
 expected_kind:composition_kind;expected_numeric_stores:list Z}.
Definition simple_case fields parent observed expected stores :=
 Build_composition_case fields parent observed discard_bytes none_bytes none_bytes[ValidationStructure.shell_bytes]expected stores.
Definition composition_cases :=
 [simple_case minimal_fields(text_bytes "42"%string)(Int.repr 42)(initialization_first(initialization_ready 8))minimal_values;
  simple_case(replace_field 0[])(text_bytes "0"%string)(Int.repr 17)(numeric_first 0)[];
  simple_case(replace_field 4(text_bytes "18446744073709551616"%string))(text_bytes "0"%string)(Int.repr 17)(numeric_first 4)(firstn 4 minimal_values);
  simple_case(replace_field 9[])(text_bytes "42"%string)(Int.repr 41)(numeric_first 9)(firstn 9 minimal_values);
  Build_composition_case(replace_field 9[])[](Int.repr 0)[][][][[]](numeric_first 9)(firstn 9 minimal_values);
  Build_composition_case minimal_fields[](Int.repr 42)[][][][[]](parent_first false)minimal_values;
  Build_composition_case minimal_fields(text_bytes "42"%string)(Int.repr 41)[][][][[]](parent_first true)minimal_values;
  Build_composition_case minimal_fields(text_bytes "42"%string)(Int.repr 42)[][][][[]](initialization_first rejected_export)minimal_values]++
 map(fun c=>simple_case minimal_fields(case_bytes c)(case_observed c)
  (if case_rejected c then parent_first(negb(parent_guard_bad(NumberMath.decimal_number(case_bytes c))))
   else initialization_first(initialization_ready 8))minimal_values)parent_cases++
 map(fun c=>Build_composition_case(map(decimal_digits 21)(InitializationSamples.numeric_values c))(text_bytes "42"%string)(Int.repr 42)
  (export_text c)(tree_text c)(stdin_text c)(guest_texts c)(initialization_first(expected_result c))(InitializationSamples.numeric_values c))initialization_cases.

Definition composition_case_valid c := Nat.eqb(List.length(numeric_texts c))10&&
 forallb digest_input_admissibleb(numeric_texts c)&&digest_input_admissibleb(parent_text c)&&
 digest_input_admissibleb(export_option c)&&digest_input_admissibleb(tree_option c)&&digest_input_admissibleb(stdin_option c)&&
 sources_admissibleb(guest_sources c).
Theorem composition_cases_valid : Forall(fun c=>composition_case_valid c=true)composition_cases.
Proof. repeat(apply Forall_cons;[vm_compute;reflexivity|]);constructor. Qed.
Theorem composition_cases_results : Forall(fun c=>
 composition_kind_of(numeric_texts c)(parent_text c)(observed_parent c)(export_option c)(tree_option c)(stdin_option c)(guest_sources c)=expected_kind c /\
 field_values(numeric_texts c)=expected_numeric_stores c)composition_cases.
Proof. repeat(apply Forall_cons;[split;vm_compute;reflexivity|]);constructor. Qed.
Theorem composition_case_count : List.length composition_cases=67%nat.
Proof. reflexivity. Qed.
