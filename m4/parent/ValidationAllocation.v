(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Library FreshMemoryDraft ScalarMemory.
From LeanCageMainNumber Require Import NumberMemory.
From LeanCageMain Require Import Main MainStructure MainMemory.
From LeanCageArguments Require Import ArgumentMemory ArgumentAllocation.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationAllocation ValidationWitnesses.
From LeanCageInitialization Require Import StoreFrames InitializationAllocation.
From LeanCageParent Require Import ParentMemory NumericMemory ValidationLocals.
Import ListNotations.
Open Scope Z_scope.
Definition validation_separate fields output b := setup_separate b /\b<>fields /\b<>output.
Lemma validation_fresh_separate m fields output b : setup_writable m->validation_local_space m fields output->
 ~Mem.valid_block m b->validation_separate fields output b.
Proof.
 intros WRITE SPACE FRESH;destruct(validation_locals_valid _ _ _ SPACE)as[F O];split;[eapply setup_fresh_separate;eassumption|].
 split;intros EQ;subst b;contradiction.
Qed.
Theorem allocate_validation_strings base fields output sources :
 setup_writable base->validation_local_space base fields output->Forall digest_input_admissible sources->
 exists after inputs,old_memory base after /\map guest_bytes inputs=sources /\guest_strings_owned after inputs /\
 Forall(fun arg=>validation_separate fields output(address_block(guest_pointer arg)))inputs /\
 setup_writable after /\validation_local_space after fields output.
Proof.
 intros WRITE SPACE VALID;revert base WRITE SPACE;induction VALID as[|bytes rest VALID REST IH];intros base WRITE SPACE.
 - exists base,[];split;[apply Mem.unchanged_on_refl|];split;[reflexivity|];split;[constructor|];split;[constructor|auto].
 - destruct(allocate_fresh_string base bytes VALID)as[mid[p[OLD[OWN FRESH]]]].
   assert(SEP:validation_separate fields output(address_block p))by(eapply validation_fresh_separate;eassumption).
   assert(WRITE':setup_writable mid)by(eapply setup_writable_old;eassumption).
   assert(SPACE':validation_local_space mid fields output)by(eapply validation_locals_old;eassumption).
   destruct(IH mid WRITE' SPACE')as[after[inputs[MORE[BYTES[STRINGS[SEPARATE[WRITABLE LOCAL]]]]]]].
   exists after,({|guest_pointer:=p;guest_bytes:=bytes|}::inputs);split;[eapply validation_old_trans;eassumption|].
   split;[cbn;rewrite BYTES;reflexivity|];split.
   + constructor;[eapply old_memory_string;eassumption|exact STRINGS].
   + split;[constructor;[exact SEP|exact SEPARATE]|auto].
Qed.
Theorem allocate_validation_table base fields output inputs : setup_writable base->validation_local_space base fields output->
 guest_strings_owned base inputs->Z.of_nat(length inputs)<=2147483647-2->
 exists after argv,old_memory base after /\guest_table_span Ptrofs.zero(2+Z.of_nat(length inputs)) /\
 guest_arguments_owned after argv Ptrofs.zero 2 inputs /\validation_separate fields output argv /\
 setup_writable after /\validation_local_space after fields output.
Proof.
 intros WRITE SPACE OWN COUNT;set(argc:=2+Z.of_nat(length inputs));set(size:=8*argc).
 destruct(Mem.alloc base 0 size)as[allocated argv]eqn:ALLOC.
 assert(FRESH:~Mem.valid_block base argv)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 assert(VALID:Forall(scalar_valid size)(guest_cells 2 inputs)).
 { apply guest_cells_valid;[lia|unfold argc;lia]. }
 destruct(scalar_stores_exist argv size(guest_cells 2 inputs)allocated VALID)as[after STORES].
 { red;intros pos RANGE;eapply Mem.perm_alloc_2;[exact ALLOC|exact RANGE]. }
 assert(OLD:old_memory base after).
 { eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
   eapply Mem.unchanged_on_implies;[eapply scalar_stores_outside;[exact STORES|exact VALID]|].
   intros b pos VALIDBASE VALIDALLOC;left;intro EQ;subst;contradiction. }
 exists after,argv;split;[exact OLD|];split.
 - unfold guest_table_span;change(Ptrofs.unsigned Ptrofs.zero)with 0.
   change Ptrofs.modulus with 18446744073709551616;lia.
 - split.
   + apply guest_table_from_cells with(argc:=argc);
     [lia|unfold argc;lia|unfold argc;change Ptrofs.modulus with 18446744073709551616;lia| |].
     * eapply old_guest_strings;eassumption.
     * apply Forall_forall;intros c IN;eapply scalar_stores_fields;
       [exact STORES|apply scalar_orderedb_sound;apply guest_cells_ordered|exact IN].
   + split;[eapply validation_fresh_separate;eassumption|];split;
     [eapply setup_writable_old;eassumption|eapply validation_locals_old;eassumption].
Qed.
Theorem allocated_validation_storage sources : Forall digest_input_admissible sources->
 Z.of_nat(length sources)<=2147483647-2->
 exists initial before fields output argv inputs,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\map guest_bytes inputs=sources /\
 guest_table_span Ptrofs.zero(2+Z.of_nat(length inputs)) /\guest_arguments_owned before argv Ptrofs.zero 2 inputs /\
 validation_separate fields output argv /\Forall(fun arg=>validation_separate fields output(address_block(guest_pointer arg)))inputs /\
 validation_local_space before fields output /\setup_writable before /\literals_owned before /\policy_writable before main_policy_block /\
 setup_separate fields /\setup_separate output /\numeric_literal_separation fields /\parent_literal_separation output.
Proof.
 intros VALID COUNT;destruct allocate_validation_locals as[initial[locals[fields[output[INIT[OLD[SPACE[WRITE[LITERALS[POLICY[FSEP[OSEP[FLIT OLIT]]]]]]]]]]]]].
 destruct(allocate_validation_strings locals fields output sources WRITE SPACE VALID)as[strings[inputs[STRINGS[BYTES[OWN[SEP[WRITE' SPACE']]]]]]].
 assert(LENGTH:length inputs=length sources)by(rewrite<-BYTES,length_map;reflexivity).
 destruct(allocate_validation_table strings fields output inputs WRITE' SPACE' OWN ltac:(lia))as[before[argv[TABLE[SPAN[ARGS[ASEP[WRITE'' SPACE'']]]]]]].
 assert(ALL:old_memory initial before)by(eapply validation_old_trans;[exact OLD|];eapply validation_old_trans;eassumption).
 assert(MORE:old_memory locals before)by(eapply validation_old_trans;eassumption).
 exists initial,before,fields,output,argv,inputs;split;[exact INIT|];split;[exact ALL|];split;[exact BYTES|];split;[exact SPAN|];split;[exact ARGS|].
 split;[exact ASEP|];split;[exact SEP|];split;[exact SPACE''|];split;[exact WRITE''|];split;[eapply literals_old;eassumption|].
 split;[eapply old_policy_writable;eassumption|];split;[exact FSEP|];split;[exact OSEP|];split;assumption.
Qed.
