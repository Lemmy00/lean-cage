(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.cases: Each table row has an actual allocated complete-composition execution. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine Library FreshMemoryDraft ScalarMemory.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainFields MainEntry MainSource MainOutcomes.
From LeanCageArguments Require Import ArgumentMemory ArgumentWitnesses.
From LeanCageArguments Require Import ArgumentSamples.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues.
From LeanCageInitialization Require Import ConfigurationMemory InitializationSource InitializationWitnesses.
From LeanCageParent Require Import ParentMachine ParentStructure ParentFinish ParentDecision ParentFrontier
 ParentTrace TraceRegion TraceExecution TraceChoices TraceInitialization NumericTrace NumericWitnesses
 ValidationInputs InputRepresentation CompositionDecision.
Import ListNotations.
Open Scope Z_scope.

From LeanCageParent Require Import CompositionExecution CompositionSamples CompositionLoss.
Theorem composition_samples_source cell c : In c composition_cases->
 exists initial before fields output argv inputs export tree stdin x rest initialized numeric_count numeric base events endpoint,
 numeric_values inputs=expected_numeric_stores c /\
 (Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 validation_input_representation before fields argv (numeric_texts c) (parent_text c) (export_option c) (tree_option c) (stdin_option c) (guest_sources c)
 inputs export tree stdin x rest /\
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(numeric_values inputs)numeric /\
 parent_steps main_ge cell(live(State f_main numeric_region Kstop(validation_locals fields output)
 (argument_witness_env argv(16+Z.of_nat(length (guest_sources c))))before))events(live endpoint) /\
 Forall(fun value=>value=(observed_parent c))(observations events) /\
 composed_endpoint(validation_locals fields output)base numeric inputs numeric_count argv (parent_text c) (observed_parent c) output
 (export_option c) (tree_option c) (stdin_option c) (guest_sources c) tree stdin x rest events endpoint /\
 (numeric_complete inputs=true->
  (parent_decision (parent_text c) (observed_parent c)=true->exists final middle,number_post numeric output Ptrofs.zero(decimal_number (parent_text c))middle /\
   endpoint=parent_endpoint(validation_locals fields output)final Kstop middle true) /\
  (parent_decision (parent_text c) (observed_parent c)=false->matching_history (parent_text c)(observations events)))) /\
 (forall first tail,events=first++tail->exists middle,
  parent_steps main_ge cell(live(State f_main numeric_region Kstop(validation_locals fields output)
   (argument_witness_env argv(16+Z.of_nat(length(guest_sources c))))before))first(live middle) /\
  parent_steps main_ge cell(live middle)tail(live endpoint) /\
  parent_steps main_ge cell(live(State f_main numeric_region Kstop(validation_locals fields output)
   (argument_witness_env argv(16+Z.of_nat(length(guest_sources c))))before))(first++[parent_loss])(dead(memory_of middle))).
Proof.
 intros IN;pose proof composition_cases_valid as VALID;pose proof composition_cases_results as RESULTS.
 rewrite Forall_forall in VALID,RESULTS;specialize(VALID c IN);specialize(RESULTS c IN).
 unfold composition_case_valid in VALID;rewrite !andb_true_iff in VALID.
 destruct VALID as[[[[[[LEN NUM]P]E]T]S]G];apply Nat.eqb_eq in LEN.
 assert(NUMVALID:Forall digest_input_admissible(numeric_texts c)).
 { apply Forall_forall;intros bytes PRESENT;apply digest_input_admissible_sound.
   rewrite forallb_forall in NUM;apply NUM;exact PRESENT. }
 destruct(allocated_composition_execution cell(numeric_texts c)(parent_text c)(export_option c)(tree_option c)(stdin_option c)(guest_sources c)(observed_parent c)
 LEN NUMVALID(digest_input_admissible_sound _ P)(digest_input_admissible_sound _ E)
 (digest_input_admissible_sound _ T)(digest_input_admissible_sound _ S)(sources_admissible_sound _ G))
 as(initial & before & fields & output & argv & inputs & export & tree & stdin & x & rest & initialized & numeric_count & numeric & base & events & endpoint & EXEC).
 exists initial,before,fields,output,argv,inputs,export,tree,stdin,x,rest,initialized,numeric_count,numeric,base,events,endpoint.
 pose proof EXEC as(INIT & OLD & REP & FIELDS & STORES & RUN & REST).
 split.
 - pose proof(representation_numeric_data before fields argv(numeric_texts c)(parent_text c)(export_option c)(tree_option c)(stdin_option c)(guest_sources c)inputs export tree stdin x rest REP)as[NUMBYTES GUESTBYTES].
   rewrite numeric_values_data,NUMBYTES;exact(proj2 RESULTS).
 - split;[exact EXEC|];intros first tail EQ;eapply composed_prefix_loss;[exact RUN|exact EQ].
Qed.
