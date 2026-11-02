(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine Library FreshMemoryDraft.
From LeanCageMainNumber Require Import NumberMath NumberStorage.
From LeanCageMain Require Import Main MainStructure.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentMachine ParentStructure ParentFinish ParentAllocation ParentWitnesses ParentDecision.
Import ListNotations.
Open Scope Z_scope.
Record parent_case := {case_bytes:list byte;case_observed:int;case_rejected:bool}.
Definition parent_cases := [
 Build_parent_case(map Byte.repr[49])(Int.repr(1))false;
 Build_parent_case(map Byte.repr[52;50])(Int.repr(42))false;
 Build_parent_case(map Byte.repr[48;48;48;52;50])(Int.repr(42))false;
 Build_parent_case(map Byte.repr[50;49;52;55;52;56;51;54;52;55])(Int.repr(2147483647))false;
 Build_parent_case(map Byte.repr[48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;48;49])(Int.repr(1))false;
 Build_parent_case(map Byte.repr[49;48;48;48;48;48;48;48;48;48])(Int.repr(1000000000))false;
 Build_parent_case(map Byte.repr[])(Int.repr(42))true;
 Build_parent_case(map Byte.repr[48])(Int.repr(0))true;
 Build_parent_case(map Byte.repr[48;48;48])(Int.repr(0))true;
 Build_parent_case(map Byte.repr[45;49])(Int.repr(-1))true;
 Build_parent_case(map Byte.repr[43;49])(Int.repr(1))true;
 Build_parent_case(map Byte.repr[32;49])(Int.repr(1))true;
 Build_parent_case(map Byte.repr[49;32])(Int.repr(1))true;
 Build_parent_case(map Byte.repr[49;120])(Int.repr(1))true;
 Build_parent_case(map Byte.repr[49;128])(Int.repr(1))true;
 Build_parent_case(map Byte.repr[50;49;52;55;52;56;51;54;52;56])(Int.repr(-2147483648))true;
 Build_parent_case(map Byte.repr[52;50;57;52;57;54;55;50;57;55])(Int.repr(1))true;
 Build_parent_case(map Byte.repr[49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;53])(Int.repr(-1))true;
 Build_parent_case(map Byte.repr[49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;54])(Int.repr(1))true;
 Build_parent_case(map Byte.repr[52;50])(Int.repr(41))true;
 Build_parent_case(map Byte.repr[52;50])(Int.repr(43))true;
 Build_parent_case(map Byte.repr[52;50])(Int.repr(0))true;
 Build_parent_case(map Byte.repr[52;50])(Int.repr(-1))true;
 Build_parent_case(map Byte.repr[50;49;52;55;52;56;51;54;52;55])(Int.repr(-2147483648))true
].
Theorem parent_cases_valid : Forall(fun c=>digest_input_admissibleb(case_bytes c)=true)parent_cases.
Proof. repeat(apply Forall_cons;[vm_compute;reflexivity|]);constructor. Qed.
Theorem parent_cases_results : Forall(fun c=>parent_decision(case_bytes c)(case_observed c)=case_rejected c)parent_cases.
Proof. repeat(apply Forall_cons;[vm_compute;reflexivity|]);constructor. Qed.
Theorem parent_case_counts :
 (length parent_cases,length(filter(fun c=>negb(case_rejected c))parent_cases))=(24,6)%nat.
Proof. split;reflexivity. Qed.
Theorem parent_samples_source cell c : In c parent_cases->
 exists initial before argv output count after events final,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 number_post before output Ptrofs.zero(decimal_number(case_bytes c))after /\
 parent_steps main_ge cell(live(State f_main(validation_suffix 15)Kstop(parent_witness_locals output)(parent_witness_env argv)before))
 events(live(parent_endpoint(parent_witness_locals output)final Kstop after(case_rejected c))) /\
 (parent_cost events<=count)%nat /\validation_frame(parent_witness_env argv)final.
Proof.
 intros IN;pose proof parent_cases_valid as VALID;pose proof parent_cases_results as RESULT.
 rewrite Forall_forall in VALID,RESULT;specialize(VALID c IN);specialize(RESULT c IN).
 rewrite<-RESULT;apply allocated_parent_decision;apply digest_input_admissible_sound;exact VALID.
Qed.
