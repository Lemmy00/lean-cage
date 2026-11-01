(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.plan: Accepted/rejected imported values share actual allocated source runs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Clight.
Require Import Machine.
From LeanCageController Require Import NumberStructure NumberMath NumberMemory NumberStorage
 NumberAllocation NumberSamples.
From LeanCagePlan Require Import PlanCodec PlanSource.
Import ListNotations.
Open Scope Z_scope.
Theorem plan_samples_match : Forall (fun sample => plan_result(fst sample)=snd sample) number_samples.
Proof.
 pose proof number_samples_checked as ALL;rewrite Forall_forall in ALL.
 apply Forall_forall;intros sample IN;unfold plan_result;rewrite plan_parser_value.
 specialize(ALL sample IN);exact(proj2(proj2 ALL)).
Qed.
Theorem plan_maximum_accepted : plan_parsed
 (decimal_bytes [49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;53])=Some(Z.to_nat decimal_max).
Proof. apply plan_parser_some;rewrite Z2Nat.id by (unfold decimal_max;lia);apply decimal_maximum_accepted. Qed.
Theorem plan_overflow_rejected : plan_parsed
 (decimal_bytes [49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;54])=None.
Proof. apply plan_parser_none;apply decimal_overflow_rejected. Qed.
Theorem plan_samples_actual_source ge cell sample : In sample number_samples ->
 plan_result(fst sample)=snd sample /\
 (exists allocated block m count after,
 Mem.alloc Mem.empty 0 (Z.of_nat(length(number_allocation_bytes(fst sample))))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte(number_allocation_bytes(fst sample)))=Some m /\
 number_input m block Ptrofs.zero (fst sample) /\ number_output m block Ptrofs.zero /\
 number_post m block Ptrofs.zero (snd sample) after /\
 steps ge cell (live(number_initial (Vptr block Ptrofs.zero) (Vptr block Ptrofs.zero) Kstop m))
 (repeat (source_step E0) count) (live(Returnstate(number_code(snd sample)) Kstop after))) /\
 (exists allocated block before m out count after,
 Mem.alloc Mem.empty 0 (Z.of_nat(length(number_allocation_bytes(fst sample))))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte(number_allocation_bytes(fst sample)))=Some before /\
 Mem.alloc before 0 8=(m,out) /\ block<>out /\
 number_input m block Ptrofs.zero (fst sample) /\ number_output m out Ptrofs.zero /\
 number_post m out Ptrofs.zero (snd sample) after /\
 steps ge cell (live(number_initial (Vptr block Ptrofs.zero) (Vptr out Ptrofs.zero) Kstop m))
 (repeat (source_step E0) count) (live(Returnstate(number_code(snd sample)) Kstop after))).
Proof.
 intros MEMBER;split.
 - pose proof plan_samples_match as ALL;rewrite Forall_forall in ALL;exact(ALL sample MEMBER).
 - apply number_samples_actual_source;exact MEMBER.
Qed.
