(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Explicit allocated witnesses, rooted in complete-program initial memory. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
Require Import Readers ScalarMemory.
From LeanCageMainNumber Require Import NumberMemory.
From LeanCageMain Require Import Main MainStructure MainMemory MainEntry MainGlobals MainPacked MainArgv.
Import ListNotations.
Open Scope Z_scope.
Definition allocated_numeric_input textfields fields argv inputs m :=
 exists global allocated strings block fields_memory argv_memory,
 Genv.init_mem Main.prog=Some global /\
 Mem.alloc global 0(Z.of_nat(length(packed_bytes textfields)))=(allocated,block) /\
 Mem.storebytes allocated block 0(map Byte(packed_bytes textfields))=Some strings /\
 inputs=packed_inputs block 0 textfields /\
 Mem.alloc strings 0 80=(fields_memory,fields) /\
 Mem.alloc fields_memory 0 96=(argv_memory,argv) /\
 scalar_stores argv argv_memory(argv_cells 0 inputs)m.
Lemma writable_policy_valid m policy : policy_writable m policy -> Mem.valid_block m policy.
Proof.
 intros OWN;destruct(OWN 0 ltac:(lia))as[BOUND ACCESS];eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.
Theorem allocate_numeric_input textfields : length textfields=10%nat ->
 Forall(fun bytes=>Forall(fun b=>b<>Byte.zero)bytes)textfields ->
 Z.of_nat(length(packed_bytes textfields))<=Ptrofs.modulus ->
 exists fields argv inputs m,
 allocated_numeric_input textfields fields argv inputs m /\
 map input_bytes inputs=textfields /\ length inputs=10%nat /\
 numeric_entry_buffers m fields argv Ptrofs.zero inputs.
Proof.
 intros LEN NOZERO SIZE;destruct native_initial_memory_exists as[global INIT].
 pose proof(proj2(native_policy_permissions global INIT))as POLICY.
 destruct(allocated_bytes global(packed_bytes textfields))as[allocated[block[strings[ALLOC[STORE LOAD]]]]].
 assert(BP : block<>main_policy_block).
 { intro EQ;subst block;eapply Mem.fresh_block_alloc;[exact ALLOC|apply writable_policy_valid;exact POLICY]. }
 assert(STRING_POLICY : policy_writable strings main_policy_block).
 { eapply policy_writable_after_storebytes;[exact STORE|]. eapply policy_writable_after_alloc;eassumption. }
 set(inputs:=packed_inputs block 0 textfields).
 assert(INPUTS : inputs_owned strings inputs).
 { apply packed_inputs_owned;[exact NOZERO|lia|lia|exact LOAD]. }
 assert(INPUTS_POLICY : Forall(fun x=>input_block x<>main_policy_block)inputs).
 { eapply Forall_impl;[|apply packed_inputs_block]. intros x EQ;rewrite EQ;exact BP. }
 assert(INPUTS_LENGTH : length inputs=10%nat)by(unfold inputs;rewrite packed_inputs_length;exact LEN).
 destruct(Mem.alloc strings 0 80)as[fields_memory fields]eqn:FIELDS.
 assert(FP : fields<>main_policy_block).
 { intro EQ;subst fields;eapply Mem.fresh_block_alloc;[exact FIELDS|apply writable_policy_valid;exact STRING_POLICY]. }
 destruct(inputs_owned_after_alloc _ _ _ _ _ _ FIELDS INPUTS)as[F_INPUTS FSEP].
 assert(F_POLICY : policy_writable fields_memory main_policy_block)by(eapply policy_writable_after_alloc;eassumption).
 destruct(Mem.alloc fields_memory 0 96)as[argv_memory argv]eqn:ARGV.
 assert(AP : argv<>main_policy_block).
 { intro EQ;subst argv;eapply Mem.fresh_block_alloc;[exact ARGV|apply writable_policy_valid;exact F_POLICY]. }
 assert(AF : argv<>fields).
 { intro EQ;subst argv;eapply Mem.fresh_block_alloc;[exact ARGV|eapply Mem.valid_new_block;exact FIELDS]. }
 destruct(inputs_owned_after_alloc _ _ _ _ _ _ ARGV F_INPUTS)as[A_INPUTS ASEP].
 assert(A_POLICY : policy_writable argv_memory main_policy_block)by(eapply policy_writable_after_alloc;eassumption).
 assert(A_RANGE : Mem.range_perm argv_memory argv 0 96 Cur Freeable).
 { red;intros pos BOUND;eapply Mem.perm_alloc_2;eassumption. }
 destruct(argv_initialization_exists argv argv_memory inputs INPUTS_LENGTH A_RANGE)as[m ASTORES].
 assert(M_INPUTS : inputs_owned m inputs)by(eapply inputs_owned_after_stores;eassumption).
 assert(M_POLICY : policy_writable m main_policy_block)by(eapply policy_writable_after_stores;eassumption).
 assert(F_RANGE : Mem.range_perm m fields 0 80 Cur Freeable).
 { red;intros pos BOUND;apply(scalar_stores_permissions _ _ _ _ ASTORES).
   eapply Mem.perm_alloc_1;[exact ARGV|]. eapply Mem.perm_alloc_2;[exact FIELDS|exact BOUND]. }
 exists fields,argv,inputs,m;split.
 - exists global,allocated,strings,block,fields_memory,argv_memory.
   split;[exact INIT|]. split;[exact ALLOC|]. split;[exact STORE|]. split;[reflexivity|].
   split;[exact FIELDS|]. split;[exact ARGV|exact ASTORES].
 - split;[apply packed_inputs_data|]. split;[exact INPUTS_LENGTH|].
   split;[exact FP|]. split;[exact AP|]. split;[exact AF|].
   split;[change(0+96<=18446744073709551616);lia|]. split;[exact FSEP|].
   split;[apply initialized_arguments with(before:=argv_memory);assumption|]. split;assumption.
Qed.
