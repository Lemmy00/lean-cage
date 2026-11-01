(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine Library FreshMemoryDraft WriteAll.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
From LeanCageMain Require Import Main MainStructure.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentMachine ParentRegion ParentStructure ParentParse ParentFinish ParentControl
 ParentAfterParse ParentSource ParentAllocation ParentRuns ParentDecision.
Import ListNotations.
Open Scope nat_scope.
Theorem allocated_parent_certificate cell bytes : digest_input_admissible bytes->
 exists initial before argv output count after,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 number_post before output Ptrofs.zero(decimal_number bytes)after /\
 parent_certificate main_ge cell(number_memory before output Ptrofs.zero(decimal_number bytes))
 (parent_frontier(parent_witness_locals output)(parent_witness_env argv)Kstop after(decimal_number bytes))
 (9+count+28)(State f_main(validation_suffix 15)Kstop(parent_witness_locals output)(parent_witness_env argv)before).
Proof.
 intros VALID;destruct(allocated_parent_inputs bytes VALID)as[initial[before[argv[p[output[INIT[OLD[INPUT[OUTPUT TABLE]]]]]]]]].
 destruct(parent_source_certificate cell(parent_witness_locals output)(parent_witness_env argv)before Kstop argv Ptrofs.zero p bytes output
 ltac:(unfold parent_witness_locals;WriteAll.lookup)ltac:(intros _;unfold parent_witness_locals;WriteAll.lookup)
 ltac:(unfold parent_witness_locals;apply PTree.gss)ltac:(unfold parent_witness_env;apply PTree.gss)
 ltac:(rewrite Ptrofs.add_zero_l;exact TABLE)INPUT OUTPUT)as[count[after[POST CERT]]].
 exists initial,before,argv,output,count,after;auto.
Qed.
Theorem allocated_parent_decision cell bytes observed : digest_input_admissible bytes->
 exists initial before argv output count after events final,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 number_post before output Ptrofs.zero(decimal_number bytes)after /\
 parent_steps main_ge cell(live(State f_main(validation_suffix 15)Kstop(parent_witness_locals output)(parent_witness_env argv)before))
 events(live(parent_endpoint(parent_witness_locals output)final Kstop after(parent_decision bytes observed))) /\
 parent_cost events<=count /\validation_frame(parent_witness_env argv)final.
Proof.
 intros VALID;destruct(parent_guard_bad(decimal_number bytes))eqn:BAD.
 - destruct(allocated_parent_certificate cell bytes VALID)as[initial[before[argv[output[count[after[INIT[OLD[POST CERT]]]]]]]]].
   destruct(parent_actual _ _ _ _ _ _ CERT)as[events[endpoint[RUN[COST[MEM END]]]]].
   unfold parent_frontier in END;rewrite BAD in END;destruct END as[final[FRAME END]];subst endpoint.
   exists initial,before,argv,output,(9+count+28),after,events,final.
   unfold parent_decision;rewrite BAD;cbn[orb];split;[exact INIT|];split;[exact OLD|];split;[exact POST|];split;[exact RUN|];split;[exact COST|exact FRAME].
 - destruct(allocated_parent_inputs bytes VALID)as[initial[before[argv[p[output[INIT[OLD[INPUT[OUTPUT TABLE]]]]]]]]].
   destruct(decimal_number bytes)as[value|]eqn:PARSED;[|discriminate BAD].
   assert(RANGE:(0<value<=2147483647)%Z).
   { pose proof(proj1(decimal_number_exact bytes value)PARSED)as[NE[DIG[FOLD RANGE]]].
     unfold parent_guard_bad in BAD;apply Bool.orb_false_iff in BAD;destruct BAD as[NZ UPPER].
     apply Z.eqb_neq in NZ;apply Z.ltb_ge in UPPER;lia. }
   destruct(parent_observation_execution cell(parent_witness_locals output)(parent_witness_env argv)before Kstop argv Ptrofs.zero p bytes output value
    ltac:(unfold parent_witness_locals;WriteAll.lookup)ltac:(unfold parent_witness_locals;WriteAll.lookup)
    ltac:(unfold parent_witness_locals;apply PTree.gss)ltac:(unfold parent_witness_env;apply PTree.gss)
    ltac:(rewrite Ptrofs.add_zero_l;exact TABLE)INPUT OUTPUT PARSED RANGE)as[count[after[POST RUN]]].
   destruct(RUN observed 0)as[final[suffix[ACTUAL[FRAME REG]]]].
   set(events:=repeat parent_internal count++repeat parent_wait 0++parent_observed observed::repeat parent_internal suffix).
   exists initial,before,argv,output,(parent_cost events),after,events,final.
   split;[exact INIT|];split;[exact OLD|];split;[exact POST|];split.
   + unfold parent_decision;rewrite PARSED,BAD;cbn[parent_value orb];exact ACTUAL.
   + split;[lia|exact FRAME].
Qed.
Theorem allocated_parent_observations cell bytes value : digest_input_admissible bytes->
 decimal_number bytes=Some value->(0<value<=2147483647)%Z->
 exists initial before argv output after count,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 number_post before output Ptrofs.zero(Some value)after /\
 forall observed waits,exists final suffix,
 parent_steps main_ge cell(live(State f_main(validation_suffix 15)Kstop(parent_witness_locals output)(parent_witness_env argv)before))
 (repeat parent_internal count++repeat parent_wait waits++parent_observed observed::repeat parent_internal suffix)
 (live(parent_endpoint(parent_witness_locals output)final Kstop after(negb(Int.eq observed(Int.repr value))))) /\
 validation_frame(parent_witness_env argv)final /\final!_t'15=Some(Vint observed).
Proof.
 intros VALID PARSED RANGE;destruct(allocated_parent_inputs bytes VALID)as[initial[before[argv[p[output[INIT[OLD[INPUT[OUTPUT TABLE]]]]]]]]].
 destruct(parent_observation_execution cell(parent_witness_locals output)(parent_witness_env argv)before Kstop argv Ptrofs.zero p bytes output value
  ltac:(unfold parent_witness_locals;WriteAll.lookup)ltac:(unfold parent_witness_locals;WriteAll.lookup)
  ltac:(unfold parent_witness_locals;apply PTree.gss)ltac:(unfold parent_witness_env;apply PTree.gss)
  ltac:(rewrite Ptrofs.add_zero_l;exact TABLE)INPUT OUTPUT PARSED RANGE)as[count[after[POST RUN]]].
 exists initial,before,argv,output,after,count;auto.
Qed.
