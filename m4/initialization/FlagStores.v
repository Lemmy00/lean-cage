(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine Library ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationMemory ValidationValues.
From LeanCageInitialization Require Import AssemblyRegions.
Import ListNotations.
Open Scope nat_scope.
Definition flag_statement input index output literal size target :=
 Ssequence(Ssequence(argv_read input index)(comparison_call input output literal size))
 (Sassign target(Eunop Onotbool(Etempvar output tint)tint)).
Definition flag_frontier after next k e le s := exists final,
 validation_frame le final /\s=State f_main next k e final after.
Definition flag_memory (before after current:mem) := current=before \/current=after.
Lemma comparison_negation m value xs ys : Int.eq value Int.zero=bytes_equal xs ys->
 sem_unary_operation Onotbool(Vint value)tint m=Some(Val.of_bool(bytes_equal xs ys)).
Proof.
 intros EQ;change(Some(Val.of_bool(negb(negb(Int.eq value Int.zero))))=Some(Val.of_bool(bytes_equal xs ys))).
 rewrite EQ,Bool.negb_involutive;reflexivity.
Qed.
Theorem flag_statement_certificate cell e le before after k next input index output literal size target b ofs argv av p bytes text :
 (0<=index<=2147483647)%Z->input<>_argv->input<>_argc->output<>_argv->output<>_argc->
 typeof target=tint->(forall locals,location_value main_ge e locals before target b ofs)->
 e!_strcmp=None->e!literal=None->In literal validation_literals->le!_argv=Some(Vptr argv av)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add av(Ptrofs.repr(8*index))))=Some(address_value p)->
 c_string before p bytes->c_string before(literal_address literal)text->
 Mem.storev Mint32 before(Vptr b ofs)(Val.of_bool(bytes_equal bytes text))=Some after->
 region_certificate main_ge cell(flag_memory before after)(flag_frontier after next k e le)10
 (State f_main(flag_statement input index output literal size target)(Kseq next k)e le before).
Proof.
 intros INDEX INAV INAC OUTAV OUTAC TYPE LOCATION STRCMP LITERAL ID ARGV LOAD OWN TEXT STORE.
 unfold flag_statement.
 eapply region_source_prepend;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
 eapply region_source_prepend;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
 eapply region_source_prepend;[left;reflexivity| |].
 - apply certified_set_edge;eapply validation_argv_value;[exact ARGV|exact INDEX|exact LOAD].
 - eapply region_source_prepend;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
   eapply comparison_general;[left;reflexivity|exact STRCMP|exact LITERAL|exact ID|apply PTree.gss|exact OWN|exact TEXT|].
   intros value EQUAL.
   eapply region_source_prepend;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
   eapply region_source_prepend;[left;reflexivity| |].
   + eapply assignment_source_edge with(v:=Val.of_bool(bytes_equal bytes text))(w:=Val.of_bool(bytes_equal bytes text)).
     * apply LOCATION.
     * apply old_expression_value;eapply value_unary;[apply value_temp;apply PTree.gss|apply comparison_negation;exact EQUAL].
     * cbn[typeof];rewrite TYPE;destruct(bytes_equal bytes text);reflexivity.
     * rewrite TYPE;eapply assign_loc_value;[reflexivity|exact STORE].
   + eapply region_source_prepend;[right;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
     apply region_stop;[right;reflexivity|].
     eexists;split;[|reflexivity].
     unfold validation_frame;split;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.
Definition preflight_target := Evar _preflight tint.
Definition export_target := Efield(Evar _policy__1 policy_type)_export_files tint.
Theorem flag_statements_actual :
 selection_check 3=flag_statement _t'294 1 _t'7 ___stringlit_130 9 preflight_target /\
 selection_check 17=flag_statement _t'285 13 _t'20 ___stringlit_132 14 export_target.
Proof. split;reflexivity. Qed.
Lemma preflight_binding : Genv.find_symbol main_ge _preflight=Some(symbol_block _preflight).
Proof. reflexivity. Qed.
Lemma preflight_location e le m : e!_preflight=None->
 location_value main_ge e le m preflight_target(symbol_block _preflight)Ptrofs.zero.
Proof. intros LOCAL;apply global_location_value;[exact LOCAL|apply preflight_binding]. Qed.
From compcert Require Import Errors.
From LeanCageMain Require Import MainFields.
Lemma export_location e le m : e!_policy__1=None->
 location_value main_ge e le m export_target main_policy_block(Ptrofs.repr 80).
Proof.
 intros GLOBAL.
 assert(LAYOUT:exists co,(genv_cenv main_ge)!_policy=Some co /\field_offset main_ge _export_files(co_members co)=OK(80,Full)).
 { apply field_lookup_sound;vm_compute;reflexivity. }
 destruct LAYOUT as[co[CO FIELD]].
 replace(Ptrofs.repr 80)with(Ptrofs.add Ptrofs.zero(Ptrofs.repr 80))by(rewrite Ptrofs.add_zero_l;reflexivity).
 eapply struct_location_value.
 - eapply location_read_value;[apply global_location_value;[exact GLOBAL|apply main_policy_binding]|].
   apply deref_loc_copy;reflexivity.
 - reflexivity.
 - exact CO.
 - exact FIELD.
Qed.
From LeanCageValidation Require Import StringSource.
Theorem preflight_certificate cell e le before k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_130=None->e!_preflight=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string before p bytes->c_string before(literal_address ___stringlit_130)check_bytes->
 Mem.valid_access before Mint32(symbol_block _preflight)0 Writable->
 exists after,Mem.store Mint32 before(symbol_block _preflight)0(Val.of_bool(bytes_equal bytes check_bytes))=Some after /\
 region_certificate main_ge cell(flag_memory before after)(flag_frontier after(selection_after 3)k e le)11
 (State f_main(validation_suffix 3)k e le before).
Proof.
 intros STRCMP LITERAL GLOBAL ARGV LOAD OWN TEXT WRITE.
 destruct(Mem.valid_access_store before Mint32(symbol_block _preflight)0(Val.of_bool(bytes_equal bytes check_bytes))WRITE)as[after STORE].
 exists after;split;[exact STORE|].
 change(validation_suffix 3)with(Ssequence(selection_check 3)(selection_after 3)).
 eapply region_source_prepend;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
 rewrite(proj1 flag_statements_actual);eapply flag_statement_certificate with(argv:=argv)(av:=ofs)(p:=p).
 - lia.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - intros;apply preflight_location;exact GLOBAL.
 - exact STRCMP.
 - exact LITERAL.
 - unfold validation_literals;do 6 right;left;reflexivity.
 - exact ARGV.
 - exact LOAD.
 - exact OWN.
 - exact TEXT.
 - exact STORE.
Qed.
Theorem export_flag_certificate cell e le before k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_132=None->e!_policy__1=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value p)->
 c_string before p bytes->c_string before(literal_address ___stringlit_132)files_bytes->
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 exists after,Mem.store Mint32 before main_policy_block 80(Val.of_bool(bytes_equal bytes files_bytes))=Some after /\
 region_certificate main_ge cell(flag_memory before after)(flag_frontier after(selection_after 17)k e le)11
 (State f_main(validation_suffix 17)k e le before).
Proof.
 intros STRCMP LITERAL GLOBAL ARGV LOAD OWN TEXT WRITE.
 destruct(Mem.valid_access_store before Mint32 main_policy_block 80(Val.of_bool(bytes_equal bytes files_bytes))WRITE)as[after STORE].
 exists after;split;[exact STORE|].
 change(validation_suffix 17)with(Ssequence(selection_check 17)(selection_after 17)).
 eapply region_source_prepend;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
 rewrite(proj2 flag_statements_actual);eapply flag_statement_certificate with(argv:=argv)(av:=ofs)(p:=p).
 - lia.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - intros;apply export_location;exact GLOBAL.
 - exact STRCMP.
 - exact LITERAL.
 - unfold validation_literals;do 2 right;left;reflexivity.
 - exact ARGV.
 - exact LOAD.
 - exact OWN.
 - exact TEXT.
 - exact STORE.
Qed.
Definition store_outside (b:block) ofs size block pos := block<>b \/(pos<ofs)%Z \/(ofs+size<=pos)%Z.
Theorem single_store_outside before after chunk b ofs value : Mem.store chunk before b ofs value=Some after->
 Mem.unchanged_on(store_outside b ofs(size_chunk chunk))before after.
Proof. intros STORE;eapply Mem.store_unchanged_on;[exact STORE|];intros pos RANGE[NE|[LOW|HIGH]];congruence||lia. Qed.
Theorem flag_region_outside before after current b ofs value : Mem.store Mint32 before b ofs value=Some after->
 flag_memory before after current->Mem.unchanged_on(store_outside b ofs 4)before current.
Proof. intros STORE [EQ | EQ];subst current;[apply Mem.unchanged_on_refl|apply single_store_outside with(chunk:=Mint32)(value:=value);exact STORE]. Qed.
Theorem flag_region_permissions before after current b ofs value : Mem.store Mint32 before b ofs value=Some after->
 flag_memory before after current->forall block pos kind perm,Mem.perm current block pos kind perm<->Mem.perm before block pos kind perm.
Proof.
 intros STORE [EQ | EQ] block pos kind perm;subst current;[tauto|];split;intros ACCESS;
 [eapply Mem.perm_store_2|eapply Mem.perm_store_1];eassumption.
Qed.
Theorem flag_store_load before after b ofs flag : Mem.store Mint32 before b ofs(Val.of_bool flag)=Some after->
 Mem.load Mint32 after b ofs=Some(Val.of_bool flag).
Proof. intros STORE;rewrite(Mem.load_store_same _ _ _ _ _ _ STORE);destruct flag;reflexivity. Qed.
