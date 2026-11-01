(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Accepted vectors and rejection after every possible store prefix. *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From compcert Require Import Integers.
From LeanCageMain Require Import MainMemory MainPacked MainOutcomes MainWitnesses.
Import ListNotations.
Open Scope Z_scope.
Fixpoint text_bytes text : list byte := match text with
 | EmptyString=>[] | String c rest=>Byte.repr(Z.of_nat(nat_of_ascii c))::text_bytes rest end.
Definition minimal_fields := map text_bytes
 ["16777216"%string;"4"%string;"1000"%string;"10000"%string;"10"%string;"1048576"%string;"64"%string;"0"%string;"0"%string;"0"%string].
Definition minimal_values : list Z := [16777216;4;1000;10000;10;1048576;64;0;0;0].
Definition replace_field (i : nat) bytes := firstn i minimal_fields++[bytes]++skipn(S i)minimal_fields.
Definition main_cases :=
 [minimal_fields;map(fun bytes=>Byte.repr 48::bytes)minimal_fields;
  replace_field 0(text_bytes "18446744073709551615"%string);
  replace_field 0(text_bytes "-1"%string);replace_field 4(text_bytes "18446744073709551616"%string);
  replace_field 9[Byte.repr 128]]++map(fun i=>replace_field i[])(seq 0 10).
Definition case_ownershipb fields := Nat.eqb(List.length fields)10 &&
 forallb(fun bytes=>forallb(fun b=>negb(Byte.eq b Byte.zero))bytes)fields &&
 Z.leb(Z.of_nat(List.length(packed_bytes fields)))Ptrofs.modulus.
Lemma case_ownership_sound fields : case_ownershipb fields=true ->
 List.length fields=10%nat /\ Forall(fun bytes=>Forall(fun b=>b<>Byte.zero)bytes)fields /\
 Z.of_nat(List.length(packed_bytes fields))<=Ptrofs.modulus.
Proof.
 unfold case_ownershipb;rewrite !andb_true_iff;intros[[LEN NONZERO]SIZE].
 apply Nat.eqb_eq in LEN;apply Z.leb_le in SIZE;split;[exact LEN|]. split;[|exact SIZE].
 rewrite forallb_forall in NONZERO;apply Forall_forall;intros bytes IN;specialize(NONZERO bytes IN).
 rewrite forallb_forall in NONZERO;apply Forall_forall;intros b INB;specialize(NONZERO b INB).
 apply negb_true_iff in NONZERO;intro EQ;subst b;discriminate NONZERO.
Qed.
Theorem main_cases_owned : forallb case_ownershipb main_cases=true.
Proof. vm_compute;reflexivity. Qed.
Theorem main_cases_results : map(fun fields=>(field_values fields,fields_complete fields))main_cases=
 [(minimal_values,true);(minimal_values,true);
  (18446744073709551615::tl minimal_values,true);([],false);
  (firstn 4 minimal_values,false);(firstn 9 minimal_values,false)]++
 map(fun i=>(firstn i minimal_values,false))(seq 0 10).
Proof. vm_compute;reflexivity. Qed.
Theorem main_cases_allocation_witnesses : forall fields,In fields main_cases ->
 forall cell k,exists local argv inputs before initialized count after final,
 MainAllocation.allocated_numeric_input fields local argv inputs before /\
 MainMemory.policy_stores MainStructure.main_policy_block 0 initialized(field_values fields)after /\
 Machine.steps MainStructure.main_ge cell
 (Machine.live(Clight.State Main.f_main MainStructure.numeric_region k(fixture_env local)(fixture_temps argv)before))
 (repeat(Machine.source_step Events.E0)count)
 (Machine.live(if fields_complete fields then Clight.State Main.f_main Clight.Sskip
   (Clight.Kseq MainStructure.after_numeric k)(fixture_env local)final after
  else MainControl.numeric_failure_state(fixture_env local)final(Clight.Kseq MainStructure.after_numeric k)after)) /\
 (forall n,(n<=count)%nat -> exists mid,
 Machine.steps MainStructure.main_ge cell
 (Machine.live(Clight.State Main.f_main MainStructure.numeric_region k(fixture_env local)(fixture_temps argv)before))
 (repeat(Machine.source_step Events.E0)n)(Machine.live mid) /\
 Machine.steps MainStructure.main_ge cell
 (Machine.live(Clight.State Main.f_main MainStructure.numeric_region k(fixture_env local)(fixture_temps argv)before))
 (repeat(Machine.source_step Events.E0)n++[Machine.loss_step])(Machine.dead(Machine.memory_of mid)) /\
 MainSource.numeric_region_memory before initialized local inputs(Machine.memory_of mid)).
Proof.
 intros fields IN cell k;pose proof main_cases_owned as OWN;rewrite forallb_forall in OWN.
 destruct(case_ownership_sound fields(OWN fields IN))as[LEN[NOZERO SIZE]].
 apply numeric_allocated_execution;assumption.
Qed.
