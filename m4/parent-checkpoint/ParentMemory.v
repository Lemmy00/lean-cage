(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Library.
From LeanCageMainNumber Require Import NumberStorage NumberSafety.
From LeanCageMain Require Import Main MainStructure MainMemory.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import ArgumentMemory.
From LeanCageValidation Require Import ValidationStructure ValidationAllocation.
Import ListNotations.
Open Scope Z_scope.
Lemma parent_memory_string before output parsed after p bytes :
 number_memory before output Ptrofs.zero parsed after->address_block p<>output->
 c_string before p bytes->c_string after p bytes.
Proof.
 intros MEMORY SEP[NZ[SPAN LOAD]];split;[exact NZ|];split;[exact SPAN|].
 eapply Mem.loadbytes_unchanged_on;[apply number_memory_outside with(parsed:=parsed);exact MEMORY| |exact LOAD].
 intros pos RANGE;left;exact SEP.
Qed.
Lemma parent_memory_arguments before output parsed after argv ofs i inputs :
 number_memory before output Ptrofs.zero parsed after->argv<>output->
 Forall(fun arg=>address_block(guest_pointer arg)<>output)inputs->
 guest_arguments_owned before argv ofs i inputs->guest_arguments_owned after argv ofs i inputs.
Proof.
 intros MEMORY TABLE SEP;revert i;induction SEP as[|x rest HEAD TAIL IH];intros i OWN;[exact I|].
 destruct OWN as[TEXT[LOAD REST]];split;[eapply parent_memory_string;eassumption|];split.
 - rewrite(number_memory_loadv_other _ _ _ _ _ _ _ _ MEMORY TABLE);exact LOAD.
 - apply IH;exact REST.
Qed.
Lemma parent_memory_policy before output parsed after values :
 number_memory before output Ptrofs.zero parsed after->main_policy_block<>output->
 policy_image before values->policy_image after values.
Proof.
 intros MEMORY SEP[LEN[RANGE READ]];split;[exact LEN|];split;[exact RANGE|].
 intros i id IN;rewrite(number_memory_loadv_other _ _ _ _ _ _ _ _ MEMORY SEP);apply READ with(id:=id);exact IN.
Qed.
Definition parent_literal_separation output := Forall(fun item=>address_block(literal_address(fst item))<>output)literal_cases.
Lemma parent_memory_literals before output parsed after :
 number_memory before output Ptrofs.zero parsed after->parent_literal_separation output->
 literals_owned before->literals_owned after.
Proof.
 intros MEMORY SEP OWN;unfold literals_owned in *;unfold parent_literal_separation in SEP;
 rewrite Forall_forall in *;intros item IN;eapply parent_memory_string;
 [exact MEMORY|apply SEP;exact IN|apply OWN;exact IN].
Qed.
Lemma parent_memory_access before output parsed after chunk b pos perm :
 number_memory before output Ptrofs.zero parsed after->Mem.valid_access before chunk b pos perm->
 Mem.valid_access after chunk b pos perm.
Proof.
 intros MEMORY[ACCESS ALIGN];split;[|exact ALIGN];intros ofs RANGE.
 apply(number_memory_permissions _ _ _ _ _ MEMORY);apply ACCESS;exact RANGE.
Qed.
