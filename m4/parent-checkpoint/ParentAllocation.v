(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine Library FreshMemoryDraft ScalarMemory WriteAll.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
From LeanCageMain Require Import Main MainStructure MainGlobals.
From LeanCageArguments Require Import ArgumentMemory ArgumentAllocation.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationWitnesses.
Import ListNotations.
Open Scope Z_scope.
Lemma parent_string_input m p bytes : c_string m p bytes->
 number_input m(address_block p)(Ptrofs.repr(address_offset p))bytes.
Proof.
 intros[NZ[[LOW[BOUND SIZE]]LOAD]];unfold number_input.
 rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;lia);auto.
Qed.
Theorem allocate_parent_cell base : exists after output,old_memory base after /\number_output after output Ptrofs.zero.
Proof.
 destruct(Mem.alloc base 0 8)as[after output]eqn:ALLOC;exists after,output;split.
 - eapply Mem.alloc_unchanged_on;exact ALLOC.
 - split;[vm_compute;discriminate|];split;[|exists 0;reflexivity].
   intros pos RANGE;eapply Mem.perm_implies;[eapply Mem.perm_alloc_2;[exact ALLOC|exact RANGE]|constructor].
Qed.
Theorem allocate_parent_table base p :
 exists after argv,old_memory base after /\
 Mem.loadv Mptr after(Vptr argv(Ptrofs.repr 96))=Some(address_value p).
Proof.
 destruct(Mem.alloc base 0 104)as[allocated argv]eqn:ALLOC.
 assert(ACCESS:Mem.valid_access allocated Mptr argv 96 Writable).
 { split;[|exists 12;reflexivity];intros pos RANGE;eapply Mem.perm_implies;[eapply Mem.perm_alloc_2;[exact ALLOC|]|constructor].
   change(96<=pos<96+8)in RANGE;lia. }
 destruct(Mem.valid_access_store _ _ _ _(address_value p)ACCESS)as[after STORE].
 assert(FRESH:~Mem.valid_block base argv)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 exists after,argv;split.
 - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
   eapply Mem.store_unchanged_on;[exact STORE|];intros pos RANGE VALID;contradiction.
 - change(Mem.load Mptr after argv 96=Some(address_value p));rewrite(Mem.load_store_same _ _ _ _ _ _ STORE).
   destruct p;reflexivity.
Qed.
Definition parent_witness_locals output := PTree.set _parent(output,tulong)empty_env.
Definition parent_witness_env argv := PTree.set _argv(Vptr argv Ptrofs.zero)(PTree.empty val).
Theorem allocated_parent_inputs bytes : digest_input_admissible bytes->
 exists initial before argv p output,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes /\number_output before output Ptrofs.zero /\
 Mem.loadv Mptr before(Vptr argv(Ptrofs.repr 96))=Some(address_value p).
Proof.
 intros VALID;destruct native_initial_memory_exists as[initial INIT].
 destruct(allocate_guest_string initial bytes(proj1 VALID)(proj2 VALID))as[strings[p[STRINGOLD OWN]]].
 destruct(allocate_parent_table strings p)as[table[argv[TABLEOLD LOAD]]].
 destruct(allocate_parent_cell table)as[before[output[CELLOLD WRITE]]].
 exists initial,before,argv,p,output;split;[exact INIT|];split.
 - eapply validation_old_trans;[exact STRINGOLD|];eapply validation_old_trans;eassumption.
 - split.
   + apply parent_string_input;eapply old_memory_string;[exact CELLOLD|].
     eapply old_memory_string;eassumption.
   + split;[exact WRITE|eapply old_memory_loadv;eassumption].
Qed.
