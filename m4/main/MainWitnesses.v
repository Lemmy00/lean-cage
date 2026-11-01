(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs: Allocated executions of the actual selected main block. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps ScalarMemory WriteAll.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainLoop MainFields MainEntry MainSource MainPacked MainAllocation MainOutcomes.
Import ListNotations.
Open Scope Z_scope.
Definition fixture_env fields := PTree.set _fields(fields,tarray(tptr tulong)10)empty_env.
Definition fixture_temps argv := PTree.set _argv(Vptr argv Ptrofs.zero)(create_undef_temps(fn_temps f_main)).
Lemma fixture_locals fields : numeric_locals(fixture_env fields)fields /\ (fixture_env fields)!_policy__1=None.
Proof. unfold numeric_locals,fixture_env;repeat split;WriteAll.lookup. Qed.
Lemma fixture_arguments argv : (fixture_temps argv)!_argv=Some(Vptr argv Ptrofs.zero).
Proof. unfold fixture_temps;apply PTree.gss. Qed.
Theorem numeric_allocated_source textfields k : length textfields=10%nat ->
 Forall(fun bytes=>Forall(fun b=>b<>Byte.zero)bytes)textfields ->
 Z.of_nat(length(packed_bytes textfields))<=Ptrofs.modulus ->
 exists fields argv inputs before initialized count after final,
 allocated_numeric_input textfields fields argv inputs before /\ map input_bytes inputs=textfields /\
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(field_values textfields)after /\
 numeric_registers final argv Ptrofs.zero(Z.of_nat(length(field_values textfields))) /\
 store_path main_ge(numeric_region_memory before initialized fields inputs)
 (State f_main numeric_region k(fixture_env fields)(fixture_temps argv)before)count
 (if fields_complete textfields then State f_main Sskip(Kseq after_numeric k)(fixture_env fields)final after
  else numeric_failure_state(fixture_env fields)final(Kseq after_numeric k)after).
Proof.
 intros LEN NOZERO SIZE;destruct(allocate_numeric_input textfields LEN NOZERO SIZE)
 as[fields[argv[inputs[before[ALLOC[DATA[INPUTS OWN]]]]]]].
 destruct(numeric_region_source before fields argv Ptrofs.zero inputs(fixture_env fields)(fixture_temps argv)k
  INPUTS OWN(proj1(fixture_locals fields))(proj2(fixture_locals fields))(fixture_arguments argv))
 as[initialized[count[after[final[STORES[POLICY[REGS PATH]]]]]]].
 exists fields,argv,inputs,before,initialized,count,after,final.
 split;[exact ALLOC|]. split;[exact DATA|]. split;[exact STORES|].
 rewrite numeric_values_data,DATA in POLICY,REGS;split;[exact POLICY|]. split;[exact REGS|].
 unfold numeric_endpoint in PATH;rewrite numeric_complete_data,DATA in PATH;exact PATH.
Qed.
Theorem numeric_allocated_execution textfields cell k : length textfields=10%nat ->
 Forall(fun bytes=>Forall(fun b=>b<>Byte.zero)bytes)textfields ->
 Z.of_nat(length(packed_bytes textfields))<=Ptrofs.modulus ->
 exists fields argv inputs before initialized count after final,
 allocated_numeric_input textfields fields argv inputs before /\
 policy_stores main_policy_block 0 initialized(field_values textfields)after /\
 steps main_ge cell(live(State f_main numeric_region k(fixture_env fields)(fixture_temps argv)before))
 (repeat(source_step E0)count)
 (live(if fields_complete textfields then State f_main Sskip(Kseq after_numeric k)(fixture_env fields)final after
  else numeric_failure_state(fixture_env fields)final(Kseq after_numeric k)after)) /\
 (forall n,(n<=count)%nat -> exists mid,
 steps main_ge cell(live(State f_main numeric_region k(fixture_env fields)(fixture_temps argv)before))
 (repeat(source_step E0)n)(live mid) /\
 steps main_ge cell(live(State f_main numeric_region k(fixture_env fields)(fixture_temps argv)before))
 (repeat(source_step E0)n++[loss_step])(dead(memory_of mid)) /\
 numeric_region_memory before initialized fields inputs(memory_of mid)).
Proof.
 intros LEN NOZERO SIZE;destruct(numeric_allocated_source textfields k LEN NOZERO SIZE)
 as[fields[argv[inputs[before[initialized[count[after[final[ALLOC[DATA[STORES[POLICY[REGS PATH]]]]]]]]]]]]].
 exists fields,argv,inputs,before,initialized,count,after,final.
 split;[exact ALLOC|]. split;[exact POLICY|]. split;[eapply store_path_actual;exact PATH|].
 intros n BOUND;eapply store_path_loss_every_prefix;eassumption.
Qed.
