(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
Require Import Readers Library FreshMemoryDraft Machine WriteAll.
From LeanCageMain Require Import Main MainStructure MainGlobals.
From LeanCageArguments Require Import StringMachine StringPath ArgumentAllocation ArgumentWitnesses.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationMemory ValidationValues
 ValidationAllocation ValidationFinish DigestCaller ExportCaller ExecutableCaller ModeCaller.
Import ListNotations.
Open Scope Z_scope.
Lemma validation_old_trans before middle after : old_memory before middle->old_memory middle after->old_memory before after.
Proof.
 intros A B;eapply Mem.unchanged_on_trans;[exact A|].
 eapply Mem.unchanged_on_implies;[exact B|];intros b pos X Y;exact Y.
Qed.
Theorem allocated_validation_input index bytes : 0<=index<=16->digest_input_admissible bytes->
 exists initial m argv p,Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\
 c_string m p bytes /\ literals_owned m /\
 Mem.loadv Mptr m(Vptr argv(Ptrofs.repr(8*index)))=Some(address_value p) /\
 ~Mem.valid_block initial(address_block p) /\ ~Mem.valid_block initial argv.
Proof.
 intros INDEX VALID;destruct native_initial_memory_exists as[initial INIT].
 destruct(allocate_fresh_string initial bytes VALID)as[strings[p[OLD[TEXT FRESH]]]].
 destruct(allocate_selected_pointer strings index p INDEX)as[m[argv[MORE[LOAD FRESHTABLE]]]].
 exists initial,m,argv,p;split;[exact INIT|];split;[eapply validation_old_trans;eassumption|].
 split;[eapply old_memory_string;eassumption|];split.
 - eapply literals_old;[exact MORE|];eapply literals_old;[exact OLD|];apply literals_initial;exact INIT.
 - split;[exact LOAD|];split;[exact FRESH|].
   intros VALIDINITIAL;apply FRESHTABLE;eapply Mem.valid_block_unchanged_on;[exact OLD|exact VALIDINITIAL].
Qed.
Theorem allocated_export_check cell bytes : digest_input_admissible bytes->
 exists initial m argv events endpoint,Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\
 string_steps main_ge cell(live(State f_main(validation_suffix 16)Kstop empty_env(argument_witness_env argv 17)m))events(live endpoint) /\
 (string_cost events<=26)%nat /\ selection_frontier 16 empty_env(argument_witness_env argv 17)Kstop m(export_bad bytes)endpoint.
Proof.
 intros VALID;destruct(allocated_validation_input 13 bytes ltac:(lia)VALID)as[initial[m[argv[p[INIT[OLD[TEXT[LITERALS[LOAD[FRESH TABLE]]]]]]]]]].
 assert(CERT:region_certificate main_ge cell(fun after=>after=m)
 (selection_frontier 16 empty_env(argument_witness_env argv 17)Kstop m(export_bad bytes))26
 (State f_main(validation_suffix 16)Kstop empty_env(argument_witness_env argv 17)m)).
 { eapply export_check_certificate with(p:=p)(argv:=argv)(ofs:=Ptrofs.zero).
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - unfold argument_witness_env;WriteAll.lookup.
   - rewrite Ptrofs.add_zero_l;exact LOAD.
   - exact TEXT.
   - owned_literal.
   - owned_literal. }
 destruct(region_actual _ _ _ _ _ _ CERT)as[events[endpoint[RUN[BOUND[MEM RESULT]]]]].
 exists initial,m,argv,events,endpoint;auto.
Qed.
Theorem allocated_mode_check cell argc bytes : Int.min_signed<=argc<=Int.max_signed->digest_input_admissible bytes->
 exists initial m argv events endpoint,Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\
 string_steps main_ge cell(live(State f_main(validation_suffix 2)Kstop empty_env(argument_witness_env argv argc)m))events(live endpoint) /\
 (string_cost events<=31)%nat /\ selection_frontier 2 empty_env(argument_witness_env argv argc)Kstop m(mode_bad argc bytes)endpoint.
Proof.
 intros RANGE VALID;destruct(allocated_validation_input 1 bytes ltac:(lia)VALID)as[initial[m[argv[p[INIT[OLD[TEXT[LITERALS[LOAD[FRESH TABLE]]]]]]]]]].
 assert(CERT:region_certificate main_ge cell(fun after=>after=m)
 (selection_frontier 2 empty_env(argument_witness_env argv argc)Kstop m(mode_bad argc bytes))31
 (State f_main(validation_suffix 2)Kstop empty_env(argument_witness_env argv argc)m)).
 { eapply mode_check_certificate with(p:=p)(argv:=argv)(ofs:=Ptrofs.zero)(argc:=argc).
   - exact RANGE.
   - unfold argument_witness_env;WriteAll.lookup.
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - unfold argument_witness_env;WriteAll.lookup.
   - rewrite Ptrofs.add_zero_l;exact LOAD.
   - exact TEXT.
   - owned_literal.
   - owned_literal. }
 destruct(region_actual _ _ _ _ _ _ CERT)as[events[endpoint[RUN[BOUND[MEM RESULT]]]]].
 exists initial,m,argv,events,endpoint;auto.
Qed.
Theorem allocated_executable_check cell bytes : digest_input_admissible bytes->
 exists initial configured m argv events endpoint,Genv.init_mem Main.prog=Some initial /\ old_memory initial configured /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.repr 128))=Some m /\
 string_steps main_ge cell(live(State f_main(validation_suffix 22)Kstop empty_env(argument_witness_env argv 17)m))events(live endpoint) /\
 (string_cost events<=34)%nat /\ selection_frontier 22 empty_env(argument_witness_env argv 17)Kstop m(executable_bad bytes)endpoint.
Proof.
 intros VALID;destruct(allocated_validation_input 16 bytes ltac:(lia)VALID)
 as[initial[configured[argv[p[INIT[OLD[TEXT[LITERALS[LOAD[FRESH TABLE]]]]]]]]]].
 pose proof(validation_policy_args_initial _ INIT)as ACCESS.
 assert(BLOCK:Mem.valid_block initial main_policy_block).
 { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
 assert(PSEP:address_block p<>main_policy_block)by(intros EQ;apply FRESH;rewrite EQ;exact BLOCK).
 assert(ASEP:argv<>main_policy_block)by(intros EQ;apply TABLE;rewrite EQ;exact BLOCK).
 destruct(Mem.valid_access_store _ _ _ _ (Vptr argv(Ptrofs.repr 128))(old_valid_access _ _ _ _ _ _ OLD ACCESS))as[m STORE].
 assert(TEXT2:c_string m p bytes)by(eapply string_store_other;eassumption).
 assert(LOAD2:Mem.loadv Mptr m(Vptr argv(Ptrofs.repr 128))=Some(address_value p))by(eapply pointer_load_store_other;eassumption).
 assert(LITERALS2:literals_owned m).
 { eapply literals_store_other;[exact STORE| |exact LITERALS].
   apply literals_separate_globals;right;right;left;reflexivity. }
 assert(ARGS:Mem.loadv Mptr m(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv(Ptrofs.repr 128))).
 { exact(Mem.load_store_same _ _ _ _ _ _ STORE). }
 assert(CERT:region_certificate main_ge cell(fun after=>after=m)
 (selection_frontier 22 empty_env(argument_witness_env argv 17)Kstop m(executable_bad bytes))34
 (State f_main(validation_suffix 22)Kstop empty_env(argument_witness_env argv 17)m)).
 { eapply executable_check_certificate with(p:=p)(argv:=argv)(ofs:=Ptrofs.repr 128).
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - exact ARGS.
   - exact LOAD2.
   - exact TEXT2.
   - owned_literal.
   - owned_literal. }
 destruct(region_actual _ _ _ _ _ _ CERT)as[events[endpoint[RUN[BOUND[MEM RESULT]]]]].
 exists initial,configured,m,argv,events,endpoint;auto 12.
Qed.
Definition digest_pointer_setup initial tree stdin m := exists configured middle,
 old_memory initial configured /\
 Mem.store Mptr configured(symbol_block _tree_digest)0(address_value tree)=Some middle /\
 Mem.store Mptr middle(symbol_block _stdin_digest)0(address_value stdin)=Some m.
Theorem allocated_digest_inputs tree_bytes stdin_bytes :
 Forall(fun b=>b<>Byte.zero)tree_bytes->Forall(fun b=>b<>Byte.zero)stdin_bytes->
 Z.of_nat(length tree_bytes+length stdin_bytes)<=158->
 exists initial m tree stdin,Genv.init_mem Main.prog=Some initial /\ digest_pointer_setup initial tree stdin m /\
 c_string m tree tree_bytes /\ c_string m stdin stdin_bytes /\ literals_owned m /\
 Mem.loadv Mptr m(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value tree) /\
 Mem.loadv Mptr m(Vptr(symbol_block _stdin_digest)Ptrofs.zero)=Some(address_value stdin).
Proof.
 intros NONZERO1 NONZERO2 LENGTH;destruct native_initial_memory_exists as[initial INIT].
 destruct(allocated_comparison_spans initial(tree_bytes++[Byte.zero])(stdin_bytes++[Byte.zero]))
 as[allocated[b[configured[ALLOC[BYTES[TREE STDIN]]]]]].
 { rewrite !length_app;cbn;lia. }
 set(tree:={|address_block:=b;address_offset:=0|}).
 set(stdin:={|address_block:=b;address_offset:=Z.of_nat(length(tree_bytes++[Byte.zero]))|}).
 assert(FRESH:~Mem.valid_block initial b)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 assert(OLD:old_memory initial configured).
 { eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
   eapply Mem.storebytes_unchanged_on;[exact BYTES|];intros pos RANGE VALID;contradiction. }
 assert(TACCESS:Mem.valid_access initial Mptr(symbol_block _tree_digest)0 Writable).
 { apply validation_pointer_initial;[exact INIT|left;reflexivity]. }
 assert(SACCESS:Mem.valid_access initial Mptr(symbol_block _stdin_digest)0 Writable).
 { apply validation_pointer_initial;[exact INIT|right;left;reflexivity]. }
 assert(TSEP:b<>symbol_block _tree_digest).
 { intros EQ;apply FRESH;rewrite EQ;eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact TACCESS|constructor]. }
 assert(SSEP:b<>symbol_block _stdin_digest).
 { intros EQ;apply FRESH;rewrite EQ;eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact SACCESS|constructor]. }
 destruct(Mem.valid_access_store _ _ _ _ (address_value tree)(old_valid_access _ _ _ _ _ _ OLD TACCESS))as[middle TS].
 assert(SMORE:Mem.valid_access middle Mptr(symbol_block _stdin_digest)0 Writable).
 { eapply Mem.store_valid_access_1;[exact TS|eapply old_valid_access;eassumption]. }
 destruct(Mem.valid_access_store _ _ _ _ (address_value stdin)SMORE)as[m SS].
 exists initial,m,tree,stdin;split;[exact INIT|];split.
 - exists configured,middle;auto.
 - split.
   + eapply string_store_other;[exact SS|exact SSEP|].
     eapply string_store_other;[exact TS|exact TSEP|];split;assumption.
   + split.
     * eapply string_store_other;[exact SS|exact SSEP|].
       eapply string_store_other;[exact TS|exact TSEP|];split;assumption.
     * split.
       -- eapply literals_store_other;[exact SS|apply literals_separate_globals;right;left;reflexivity|].
          eapply literals_store_other;[exact TS|apply literals_separate_globals;left;reflexivity|].
          eapply literals_old;[exact OLD|apply literals_initial;exact INIT].
       -- split.
          ++ eapply pointer_load_store_other;[exact SS|exact global_pointer_distinct|].
             exact(Mem.load_store_same _ _ _ _ _ _ TS).
          ++ exact(Mem.load_store_same _ _ _ _ _ _ SS).
Qed.
Theorem allocated_digest_pair_check cell tree_bytes stdin_bytes :
 Forall(fun b=>b<>Byte.zero)tree_bytes->Forall(fun b=>b<>Byte.zero)stdin_bytes->
 Z.of_nat(length tree_bytes+length stdin_bytes)<=158->
 exists initial m tree stdin events endpoint,Genv.init_mem Main.prog=Some initial /\ digest_pointer_setup initial tree stdin m /\
 string_steps main_ge cell(live(State f_main(validation_suffix 20)Kstop empty_env(create_undef_temps(fn_temps f_main))m))events(live endpoint) /\
 (string_cost events<=4300)%nat /\ digest_frontier empty_env(create_undef_temps(fn_temps f_main))Kstop m tree_bytes stdin_bytes endpoint.
Proof.
 intros NONZERO1 NONZERO2 LENGTH;destruct(allocated_digest_inputs tree_bytes stdin_bytes NONZERO1 NONZERO2 LENGTH)
 as[initial[m[tree[stdin[INIT[SETUP[TREE[STDIN[LITERALS[TL SL]]]]]]]]]].
 assert(CERT:region_certificate main_ge cell(fun after=>after=m)
 (digest_frontier empty_env(create_undef_temps(fn_temps f_main))Kstop m tree_bytes stdin_bytes)4300
 (State f_main(validation_suffix 20)Kstop empty_env(create_undef_temps(fn_temps f_main))m)).
 { eapply digest_pair_certificate with(tree:=tree)(stdin:=stdin);
   [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|exact TL|exact SL|exact TREE|exact STDIN|owned_literal]. }
 destruct(region_actual _ _ _ _ _ _ CERT)as[events[endpoint[RUN[BOUND[MEM RESULT]]]]].
 exists initial,m,tree,stdin,events,endpoint;auto 12.
Qed.
