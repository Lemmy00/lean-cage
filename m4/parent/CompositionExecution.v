(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.cases: One allocated numeric-to-initialization path with its exact first endpoint. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine Library FreshMemoryDraft ScalarMemory.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainFields MainEntry MainSource MainOutcomes.
From LeanCageArguments Require Import ArgumentMemory ArgumentWitnesses.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues.
From LeanCageInitialization Require Import ConfigurationMemory InitializationSource InitializationWitnesses.
From LeanCageParent Require Import ParentMachine ParentStructure ParentFinish ParentDecision ParentFrontier
 ParentTrace TraceRegion TraceExecution TraceChoices TraceInitialization NumericTrace NumericWitnesses
 ValidationInputs InputRepresentation CompositionDecision.
Import ListNotations.
Open Scope Z_scope.

Definition composed_endpoint e base numeric inputs numeric_count argv bytes observed output
 export_bytes tree_bytes stdin_bytes sources tree stdin (x:guest_argument) rest events endpoint :=
 if numeric_complete inputs then
 exists parser_count middle flagged tree_set configured after,
 number_post numeric output Ptrofs.zero(decimal_number bytes)middle /\
 configuration_stores middle flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.repr 128))=Some after /\
 (parent_cost events<=numeric_count+1+((9+parser_count+28)+(26*length(x::rest)+4540)))%nat /\
 (if parent_decision bytes observed then exists final,endpoint=parent_endpoint e final Kstop middle true /\
   traced_parent_frontier e base Kstop middle(decimal_number bytes)(observations events)endpoint
  else exists final,endpoint=initialization_result_state
   (initialization_result_of export_bytes tree_bytes stdin_bytes sources(numeric_values inputs))
   middle configured after e final Kstop /\matching_history bytes(observations events))
 else endpoint=numeric_failure_state e base(Kseq after_numeric Kstop)numeric /\
 observations events=[] /\(parent_cost events<=numeric_count)%nat.

Theorem allocated_composition_execution cell textfields bytes export_bytes tree_bytes stdin_bytes sources observed :
 length textfields=10%nat->Forall digest_input_admissible textfields->
 digest_input_admissible bytes->digest_input_admissible export_bytes->digest_input_admissible tree_bytes->digest_input_admissible stdin_bytes->
 admissible_guest_sources sources->
 exists initial before fields output argv inputs export tree stdin x rest initialized numeric_count numeric base events endpoint,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 validation_input_representation before fields argv textfields bytes export_bytes tree_bytes stdin_bytes sources
 inputs export tree stdin x rest /\
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(numeric_values inputs)numeric /\
 parent_steps main_ge cell(live(State f_main numeric_region Kstop(validation_locals fields output)
 (argument_witness_env argv(16+Z.of_nat(length sources)))before))events(live endpoint) /\
 Forall(fun value=>value=observed)(observations events) /\
 composed_endpoint(validation_locals fields output)base numeric inputs numeric_count argv bytes observed output
 export_bytes tree_bytes stdin_bytes sources tree stdin x rest events endpoint /\
 (numeric_complete inputs=true->
  (parent_decision bytes observed=true->exists final middle,number_post numeric output Ptrofs.zero(decimal_number bytes)middle /\
   endpoint=parent_endpoint(validation_locals fields output)final Kstop middle true) /\
  (parent_decision bytes observed=false->matching_history bytes(observations events))).
Proof.
 intros LEN NUMVALID PVALID EVALID TVALID SVALID GUEST.
 destruct(allocated_numeric_validation cell textfields bytes export_bytes tree_bytes stdin_bytes sources
 LEN NUMVALID PVALID EVALID TVALID SVALID GUEST)
 as(initial & before & fields & output & argv & inputs & export & tree & stdin & x & rest & initialized & numeric_count & numeric & base & INIT & OLD & REP & FIELDS & STORES & FRAME & CONTRACT).
 pose proof(representation_numeric_data before fields argv textfields bytes export_bytes tree_bytes stdin_bytes sources inputs export tree stdin x rest REP)as[NUMBYTES GUESTBYTES].
 unfold numeric_trace_contract in CONTRACT;unfold composed_endpoint.
 destruct(numeric_complete inputs)eqn:COMPLETE.
 - destruct CONTRACT as[parser_count[middle[flagged[tree_set[configured[after[POST[CONFIG[STORE[CERT REST]]]]]]]]]].
   destruct(trace_actual_chosen _ _ _ _ _ _ _ observed CERT)
   as[events[endpoint[RUN[COST[MEM[END ALL]]]]]].
   cbn in END;unfold traced_initialization_frontier in END.
   exists initial,before,fields,output,argv,inputs,export,tree,stdin,x,rest,initialized,numeric_count,numeric,base,events,endpoint.
   split;[exact INIT|];split;[exact OLD|];split;[exact REP|];split;[exact FIELDS|];split;[exact STORES|];split;[exact RUN|];split;[exact ALL|];rewrite COMPLETE.
   destruct END as[[HISTORY[REJECT OBS]]|[MATCH READY]].
   + pose proof(rejecting_history_decision bytes _ observed OBS ALL)as BAD.
     destruct REJECT as[FRONT[final LAST]];split.
     * exists parser_count,middle,flagged,tree_set,configured,after;split;[exact POST|];split;[exact CONFIG|];split.
       -- rewrite Ptrofs.add_zero_l in STORE;exact STORE.
       -- split;[exact COST|rewrite BAD;exists final;auto].
     * intros _;split.
       -- intros _;exists final,middle;auto.
       -- intros GOOD;congruence.
   + pose proof(matching_history_decision bytes _ observed MATCH ALL)as GOOD.
     destruct(initialization_bytes_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GUESTBYTES eq_refl READY)as[final LAST].
     split.
     * exists parser_count,middle,flagged,tree_set,configured,after;split;[exact POST|];split;[exact CONFIG|];split.
       -- rewrite Ptrofs.add_zero_l in STORE;exact STORE.
       -- split;[exact COST|rewrite GOOD;exists final;auto].
     * intros _;split;[intros BAD;congruence|intros _;exact MATCH].
 - destruct CONTRACT as[CERT REST].
   destruct(trace_actual_chosen _ _ _ _ _ _ _ observed CERT)as[events[endpoint[RUN[COST[MEM[[H LAST] ALL]]]]]].
   cbn in H.
   exists initial,before,fields,output,argv,inputs,export,tree,stdin,x,rest,initialized,numeric_count,numeric,base,events,endpoint.
   split;[exact INIT|];split;[exact OLD|];split;[exact REP|];split;[exact FIELDS|];split;[exact STORES|];split;[exact RUN|];split;[exact ALL|];rewrite COMPLETE.
   split;[split;[exact LAST|auto]|intros IMPOSSIBLE;discriminate IMPOSSIBLE].
Qed.
