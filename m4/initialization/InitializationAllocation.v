(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Library FreshMemoryDraft ScalarMemory.
From LeanCageMain Require Import Main MainStructure MainGlobals MainMemory.
From LeanCageBounds Require Import BoundsMemory BoundsWitnesses.
From LeanCageArguments Require Import ArgumentMemory ArgumentAllocation ArgumentWitnesses.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationMemory ValidationAllocation ValidationWitnesses.
From LeanCageInitialization Require Import FlagStores StoreFrames.
Import ListNotations.
Open Scope Z_scope.
Definition setup_writable m :=
 Mem.valid_access m Mint32(symbol_block _preflight)0 Writable /\
 Mem.valid_access m Mint32 main_policy_block 80 Writable /\
 Mem.valid_access m Mptr(symbol_block _tree_digest)0 Writable /\
 Mem.valid_access m Mptr(symbol_block _stdin_digest)0 Writable /\
 Mem.valid_access m Mptr main_policy_block 88 Writable.
Lemma setup_initial_writable m : Genv.init_mem Main.prog=Some m->setup_writable m.
Proof.
 intros INIT;unfold setup_writable;split.
 - assert(VAR:Genv.find_var_info(Genv.globalenv Main.prog)(symbol_block _preflight)=Some v_preflight)by reflexivity.
   pose proof(proj1(Genv.init_mem_characterization Main.prog(symbol_block _preflight)VAR INIT))as RANGE.
   split;[exact RANGE|exists 0;reflexivity].
 - split.
   + destruct(native_policy_permissions _ INIT)as[RANGE _];split;[|exists 20;reflexivity].
     intros pos BOUND;apply RANGE;change(80<=pos<80+4)in BOUND;lia.
   + split;[apply validation_pointer_initial;[exact INIT|left;reflexivity]|].
     split;[apply validation_pointer_initial;[exact INIT|right;left;reflexivity]|apply validation_policy_args_initial;exact INIT].
Qed.
Lemma setup_writable_old before after : old_memory before after->setup_writable before->setup_writable after.
Proof.
 intros OLD[A[B[C[D E]]]];unfold setup_writable;repeat split;
 try(eapply old_valid_access;[exact OLD|eassumption]).
Qed.
Lemma setup_writable_frame before after : setup_frame before after->setup_writable before->setup_writable after.
Proof.
 intros FRAME[A[B[C[D E]]]];unfold setup_writable;repeat split;
 try(eapply setup_access;[exact FRAME|eassumption]).
Qed.
Lemma setup_fresh_separate m b : setup_writable m->~Mem.valid_block m b->setup_separate b.
Proof.
 intros[A[B[C[D E]]]]FRESH;unfold setup_separate;repeat split;intros EQ;subst b;apply FRESH.
 all:eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[eassumption|constructor].
Qed.
Lemma scalar_access b before cells after : scalar_stores b before cells after->forall chunk block ofs perm,
 Mem.valid_access before chunk block ofs perm->Mem.valid_access after chunk block ofs perm.
Proof.
 intros STORES chunk block ofs perm[RANGE ALIGN];split;[|exact ALIGN];intros pos BOUND.
 apply(scalar_stores_permissions _ _ _ _ STORES);apply RANGE;exact BOUND.
Qed.
Lemma setup_writable_scalars b before cells after : scalar_stores b before cells after->setup_writable before->setup_writable after.
Proof.
 intros STORES[A[B[C[D E]]]];unfold setup_writable;
 repeat(split;[eapply scalar_access;[exact STORES|eassumption]|]);eapply scalar_access;[exact STORES|eassumption].
Qed.
Lemma scalar_string_other b before cells after p bytes : scalar_stores b before cells after->
 address_block p<>b->c_string before p bytes->c_string after p bytes.
Proof.
 intros STORES;induction STORES;intros SEP OWN;[exact OWN|].
 apply IHSTORES;[exact SEP|];destruct OWN as[NZ[SPAN LOAD]];split;[exact NZ|];split;[exact SPAN|].
 erewrite Mem.loadbytes_store_other;[exact LOAD|eassumption|auto].
Qed.
Lemma policy_literals before after values : policy_stores main_policy_block 0 before values after->
 literals_owned before->literals_owned after.
Proof.
 intros STORES OWN;unfold literals_owned in *;rewrite Forall_forall in *;intros item IN.
 pose proof setup_literal_blocks as SEP;rewrite Forall_forall in SEP.
 destruct(SEP item IN)as[A[B[C D]]];eapply scalar_string_other;[exact STORES|exact B|apply OWN;exact IN].
Qed.
Theorem allocated_setup_policy values : length values=10%nat->Forall(fun v=>0<=v<=Int64.max_unsigned)values->
 exists initial configured,Genv.init_mem Main.prog=Some initial /\policy_stores main_policy_block 0 initial values configured /\
 policy_image configured values /\setup_writable configured /\literals_owned configured.
Proof.
 intros LEN RANGE;destruct(allocated_policy_image values LEN RANGE)as[initial[configured[INIT[STORES IMAGE]]]].
 exists initial,configured;split;[exact INIT|];split;[exact STORES|];split;[exact IMAGE|];split.
 - eapply setup_writable_scalars;[exact STORES|apply setup_initial_writable;exact INIT].
 - eapply policy_literals;[exact STORES|apply literals_initial;exact INIT].
Qed.
Theorem allocate_setup_strings base sources : setup_writable base->
 Forall digest_input_admissible sources->
 exists after inputs,old_memory base after /\map guest_bytes inputs=sources /\guest_strings_owned after inputs /\
 Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))inputs /\setup_writable after.
Proof.
 intros WRITE VALID;revert base WRITE;induction VALID as[|bytes rest VALID REST IH];intros base WRITE.
 - exists base,[];split;[apply Mem.unchanged_on_refl|];split;[reflexivity|];split;[constructor|];split;[constructor|exact WRITE].
 - destruct(allocate_fresh_string base bytes VALID)as[mid[p[OLD[OWN FRESH]]]].
   assert(SEP:setup_separate(address_block p))by(eapply setup_fresh_separate;eassumption).
   assert(WRITE':setup_writable mid)by(eapply setup_writable_old;eassumption).
   destruct(IH mid WRITE')as[after[inputs[MORE[BYTES[STRINGS[SEPARATE WRITABLE]]]]]].
   exists after,({|guest_pointer:=p;guest_bytes:=bytes|}::inputs);split.
   + eapply validation_old_trans;eassumption.
   + split;[cbn;rewrite BYTES;reflexivity|];split.
     * constructor;[eapply old_memory_string;eassumption|exact STRINGS].
     * split;[constructor;[exact SEP|exact SEPARATE]|exact WRITABLE].
Qed.
Theorem allocate_setup_table base inputs : setup_writable base->guest_strings_owned base inputs->
 Z.of_nat(length inputs)<=2147483647-13->
 exists after argv,old_memory base after /\guest_table_span Ptrofs.zero(13+Z.of_nat(length inputs)) /\
 guest_arguments_owned after argv Ptrofs.zero 13 inputs /\setup_separate argv /\setup_writable after.
Proof.
 intros WRITE OWN COUNT;set(argc:=13+Z.of_nat(length inputs));set(size:=8*argc).
 destruct(Mem.alloc base 0 size)as[allocated argv]eqn:ALLOC.
 assert(FRESH:~Mem.valid_block base argv)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 assert(VALID:Forall(scalar_valid size)(guest_cells 13 inputs)).
 { apply guest_cells_valid;[lia|unfold argc;lia]. }
 destruct(scalar_stores_exist argv size(guest_cells 13 inputs)allocated VALID)as[after STORES].
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
   + split;[eapply setup_fresh_separate;eassumption|eapply setup_writable_old;eassumption].
Qed.
Theorem allocated_setup_inputs values sources :
 length values=10%nat->Forall(fun v=>0<=v<=Int64.max_unsigned)values->
 Forall digest_input_admissible sources->Z.of_nat(length sources)<=2147483647-13->
 exists initial numeric before argv inputs,
 Genv.init_mem Main.prog=Some initial /\policy_stores main_policy_block 0 initial values numeric /\
 old_memory numeric before /\map guest_bytes inputs=sources /\
 guest_table_span Ptrofs.zero(13+Z.of_nat(length inputs)) /\
 guest_arguments_owned before argv Ptrofs.zero 13 inputs /\setup_separate argv /\
 Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))inputs /\
 policy_image before values /\literals_owned before /\setup_writable before.
Proof.
 intros LEN RANGE VALID COUNT.
 destruct(allocated_setup_policy values LEN RANGE)as[initial[numeric[INIT[STORES[IMAGE[WRITE LITERALS]]]]]].
 destruct(allocate_setup_strings numeric sources WRITE VALID)as[strings[inputs[OLD[BYTES[OWN[SEP WRITE']]]]]].
 assert(LENGTH:length inputs=length sources)by(rewrite<-BYTES,length_map;reflexivity).
 destruct(allocate_setup_table strings inputs WRITE' OWN ltac:(lia))as[before[argv[MORE[SPAN[ARGS[ARGVSEP WRITE'']]]]]].
 assert(ALL:old_memory numeric before)by(eapply validation_old_trans;eassumption).
 exists initial,numeric,before,argv,inputs;split;[exact INIT|];split;[exact STORES|];split;[exact ALL|].
 split;[exact BYTES|];split;[exact SPAN|];split;[exact ARGS|];split;[exact ARGVSEP|];split;[exact SEP|];split.
 - eapply old_policy_image;eassumption.
 - split;[eapply literals_old;eassumption|exact WRITE''].
Qed.
