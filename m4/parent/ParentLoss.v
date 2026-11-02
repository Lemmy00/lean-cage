(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine Library FreshMemoryDraft WriteAll.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
From LeanCageMain Require Import Main MainStructure.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure.
From LeanCageParent Require Import ParentMachine ParentStructure ParentParse ParentControl ParentAllocation ParentRuns.
Import ListNotations.
Open Scope nat_scope.
Theorem allocated_parent_wait_loss cell bytes value : digest_input_admissible bytes->
 decimal_number bytes=Some value->(0<value<=2147483647)%Z->
 exists initial before argv output after count,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 number_post before output Ptrofs.zero(Some value)after /\
 parent_step main_ge cell(live(State f_main(validation_suffix 15)Kstop(parent_witness_locals output)(parent_witness_env argv)before))parent_loss(dead before) /\
 forall waits,parent_steps main_ge cell
 (live(State f_main(validation_suffix 15)Kstop(parent_witness_locals output)(parent_witness_env argv)before))
 (repeat parent_internal count++repeat parent_wait waits++[parent_loss])(dead after).
Proof.
 intros VALID PARSED RANGE;destruct(allocated_parent_inputs bytes VALID)as[initial[before[argv[p[output[INIT[OLD[INPUT[OUTPUT TABLE]]]]]]]]].
 destruct(parent_observation_reached(parent_witness_locals output)(parent_witness_env argv)before Kstop argv Ptrofs.zero p bytes output value
 ltac:(unfold parent_witness_locals;WriteAll.lookup)ltac:(unfold parent_witness_locals;WriteAll.lookup)
 ltac:(unfold parent_witness_locals;apply PTree.gss)ltac:(unfold parent_witness_env;apply PTree.gss)
 ltac:(rewrite Ptrofs.add_zero_l;exact TABLE)INPUT OUTPUT PARSED RANGE)as[count[after[POST PREFIX]]].
 exists initial,before,argv,output,after,(9+count+parent_guard_cost(Some value)+3).
 split;[exact INIT|];split;[exact OLD|];split;[exact POST|];split;[apply parent_loss_everywhere|].
 intros waits;eapply parent_steps_trans;[eapply parent_store_actual;exact PREFIX|apply parent_wait_then_loss].
Qed.
