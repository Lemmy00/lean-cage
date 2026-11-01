(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Library FreshMemoryDraft ScalarMemory.
From LeanCageMainNumber Require Import NumberMemory.
From LeanCageMain Require Import Main MainStructure MainMemory MainGlobals.
From LeanCageArguments Require Import ArgumentMemory.
From LeanCageValidation Require Import ValidationStructure ValidationAllocation ValidationWitnesses.
From LeanCageInitialization Require Import StoreFrames InitializationAllocation.
From LeanCageParent Require Import ParentMemory NumericMemory.
Import ListNotations.
Open Scope Z_scope.
Definition validation_local_space m fields output :=
 Mem.range_perm m fields 0 80 Cur Freeable /\number_output m output Ptrofs.zero.
Lemma validation_locals_old before after fields output : old_memory before after->
 validation_local_space before fields output->validation_local_space after fields output.
Proof.
 intros OLD[RANGE[BOUND ACCESS]];split.
 - intros pos WITHIN;eapply Mem.perm_unchanged_on;[exact OLD| |apply RANGE;exact WITHIN].
   eapply Mem.perm_valid_block;apply RANGE;exact WITHIN.
 - split;[exact BOUND|eapply old_valid_access;eassumption].
Qed.
Lemma validation_locals_valid m fields output : validation_local_space m fields output->
 Mem.valid_block m fields /\Mem.valid_block m output.
Proof.
 intros[RANGE[BOUND ACCESS]];split.
 - eapply Mem.perm_valid_block;apply RANGE with(ofs:=0);lia.
 - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.
Lemma validation_string_valid m p bytes : c_string m p bytes->Mem.valid_block m(address_block p).
Proof.
 intros[NZ[SPAN LOAD]];eapply Mem.perm_valid_block with(ofs:=address_offset p)(k:=Cur)(p:=Readable);eapply Mem.loadbytes_range_perm;[exact LOAD|].
 rewrite length_app;cbn[length];lia.
Qed.
Lemma fresh_parent_literals m b : literals_owned m->~Mem.valid_block m b->parent_literal_separation b.
Proof.
 intros OWN FRESH;unfold parent_literal_separation;unfold literals_owned in OWN;
 eapply Forall_impl;[|exact OWN];intros item TEXT EQ;apply FRESH;rewrite<-EQ;eapply validation_string_valid;exact TEXT.
Qed.
Lemma fresh_numeric_literals m b : literals_owned m->~Mem.valid_block m b->numeric_literal_separation b.
Proof.
 intros OWN FRESH;pose proof(fresh_parent_literals m b OWN FRESH)as SEP;pose proof setup_literal_blocks as SETUP.
 unfold numeric_literal_separation,parent_literal_separation in *;rewrite Forall_forall in *;intros item IN;split.
 - apply SEP;exact IN.
 - exact(proj1(proj2(SETUP item IN))).
Qed.
Lemma old_policy_writable before after : old_memory before after->policy_writable before main_policy_block->policy_writable after main_policy_block.
Proof.
 intros OLD WRITE i RANGE;destruct(WRITE i RANGE)as[BOUND ACCESS];split;[exact BOUND|eapply old_valid_access;eassumption].
Qed.
Theorem allocate_validation_locals :
 exists initial before fields output,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 validation_local_space before fields output /\setup_writable before /\literals_owned before /\
 policy_writable before main_policy_block /\setup_separate fields /\setup_separate output /\
 numeric_literal_separation fields /\parent_literal_separation output.
Proof.
 destruct native_initial_memory_exists as[initial INIT].
 pose proof(setup_initial_writable initial INIT)as WRITE;pose proof(literals_initial initial INIT)as LITERALS.
 pose proof(proj2(native_policy_permissions initial INIT))as POLICY.
 destruct(Mem.alloc initial 0 80)as[middle fields]eqn:FIELDS.
 assert(FOLD:old_memory initial middle)by(eapply Mem.alloc_unchanged_on;exact FIELDS).
 assert(FFRESH:~Mem.valid_block initial fields)by(eapply Mem.fresh_block_alloc;exact FIELDS).
 assert(FSEP:setup_separate fields)by(eapply setup_fresh_separate;eassumption).
 assert(FLIT:numeric_literal_separation fields)by(eapply fresh_numeric_literals;eassumption).
 assert(LITERALS':literals_owned middle)by(eapply literals_old;eassumption).
 assert(WRITE':setup_writable middle)by(eapply setup_writable_old;eassumption).
 destruct(Mem.alloc middle 0 8)as[before output]eqn:OUTPUT.
 assert(OOLD:old_memory middle before)by(eapply Mem.alloc_unchanged_on;exact OUTPUT).
 assert(OFRESH:~Mem.valid_block middle output)by(eapply Mem.fresh_block_alloc;exact OUTPUT).
 assert(OSEP:setup_separate output)by(eapply setup_fresh_separate;eassumption).
 assert(OLIT:parent_literal_separation output)by(eapply fresh_parent_literals;eassumption).
 assert(ALL:old_memory initial before)by(eapply validation_old_trans;eassumption).
 exists initial,before,fields,output;split;[exact INIT|];split;[exact ALL|];split.
 - split.
   + intros pos RANGE;eapply Mem.perm_alloc_1;[exact OUTPUT|];eapply Mem.perm_alloc_2;[exact FIELDS|exact RANGE].
   + split;[vm_compute;discriminate|];split;[|exists 0;reflexivity].
     intros pos RANGE;eapply Mem.perm_implies;[eapply Mem.perm_alloc_2;[exact OUTPUT|exact RANGE]|constructor].
 - split;[eapply setup_writable_old;eassumption|];split;[eapply literals_old;[exact ALL|exact LITERALS]|].
   split;[eapply old_policy_writable;eassumption|];split;[exact FSEP|];split;[exact OSEP|];split;assumption.
Qed.
