(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine Library ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath ArgumentWords.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationMemory ValidationValues.
From LeanCageInitialization Require Import FlagStores.
Import ListNotations.
Open Scope nat_scope.
Definition pointer_store_statement input index id :=
 Ssequence(argv_read input index)(Sassign(Evar id(tptr tschar))(Etempvar input(tptr tschar))).
Theorem pointer_statements_actual :
 selection_check 18=pointer_store_statement _t'284 14 _tree_digest /\
 selection_check 19=pointer_store_statement _t'283 15 _stdin_digest.
Proof. split;reflexivity. Qed.
Lemma digest_global_binding id : In id[_tree_digest;_stdin_digest]->Genv.find_symbol main_ge id=Some(symbol_block id).
Proof. intros[<-|[<-|BAD]];[reflexivity|reflexivity|contradiction]. Qed.
Theorem pointer_statement_path e le before after k next input index id argv ofs p :
 (0<=index<=2147483647)%Z->le!_argv=Some(Vptr argv ofs)->e!id=None->In id[_tree_digest;_stdin_digest]->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr(8*index))))=Some(address_value p)->
 Mem.store Mptr before(symbol_block id)0(address_value p)=Some after->
 store_path main_ge(flag_memory before after)
 (State f_main(pointer_store_statement input index id)(Kseq next k)e le before)5
 (State f_main next k e(PTree.set input(address_value p)le)after).
Proof.
 intros INDEX ARGV GLOBAL ID LOAD STORE;unfold pointer_store_statement.
 eapply store_next;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
 eapply store_next;[left;reflexivity| |].
 - apply certified_set_edge;eapply validation_argv_value;[exact ARGV|exact INDEX|exact LOAD].
 - eapply store_next;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
   eapply store_next;[left;reflexivity| |].
   + eapply assignment_source_edge with(v:=address_value p)(w:=address_value p).
     * apply global_location_value;[exact GLOBAL|apply digest_global_binding;exact ID].
     * apply old_expression_value;apply value_temp;apply PTree.gss.
     * reflexivity.
     * eapply assign_loc_value;[reflexivity|exact STORE].
   + eapply store_next;[right;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
     constructor;right;reflexivity.
Qed.
Theorem digest_pointer_certificate cell e le before k index input slot id argv ofs p :
 (index=18 \/index=19)->selection_check index=pointer_store_statement input slot id->input<>_argv->input<>_argc->
 (0<=slot<=2147483647)%Z->le!_argv=Some(Vptr argv ofs)->e!id=None->In id[_tree_digest;_stdin_digest]->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr(8*slot))))=Some(address_value p)->
 Mem.valid_access before Mptr(symbol_block id)0 Writable->
 exists after,Mem.store Mptr before(symbol_block id)0(address_value p)=Some after /\
 region_certificate main_ge cell(flag_memory before after)(flag_frontier after(selection_after index)k e le)6
 (State f_main(validation_suffix index)k e le before).
Proof.
 intros INDEX SHAPE INPUT ARGC SLOT ARGV GLOBAL ID LOAD WRITE.
 destruct(Mem.valid_access_store before Mptr(symbol_block id)0(address_value p)WRITE)as[after STORE].
 exists after;split;[exact STORE|].
 assert(SUFFIX:validation_suffix index=Ssequence(selection_check index)(selection_after index)).
 { destruct INDEX as[EQ | EQ];subst index;reflexivity. }
 rewrite SUFFIX;eapply region_source_prepend;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
 rewrite SHAPE;change 5 with(5+0).
 eapply region_store_path.
 - eapply pointer_statement_path;[exact SLOT|exact ARGV|exact GLOBAL|exact ID|exact LOAD|exact STORE].
 - apply region_stop;[right;reflexivity|].
   eexists;split;[|reflexivity];unfold validation_frame;split;rewrite PTree.gso by congruence;reflexivity.
Qed.
Definition arguments_assignment := Sassign
 (Efield(Evar _policy__1 policy_type)_args(tptr(tptr tschar)))
 (Ebinop Oadd(Etempvar _argv(tptr(tptr tschar)))(Econst_int(Int.repr 16)tint)(tptr(tptr tschar))).
Theorem arguments_assignment_actual : selection_check 21=arguments_assignment.
Proof. reflexivity. Qed.
Theorem arguments_pointer_path e le before after k argv ofs :
 e!_policy__1=None->le!_argv=Some(Vptr argv ofs)->
 Mem.store Mptr before main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after->
 store_path main_ge(flag_memory before after)(State f_main(validation_suffix 21)k e le before)3
 (State f_main(validation_suffix 22)k e le after).
Proof.
 intros GLOBAL ARGV STORE.
 change(validation_suffix 21)with(Ssequence arguments_assignment(validation_suffix 22)).
 eapply store_next;[left;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
 unfold arguments_assignment;eapply store_next;[left;reflexivity| |].
 - eapply assignment_source_edge with(v:=Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))(w:=Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128))).
   + apply policy_arguments_location;exact GLOBAL.
   + eapply binary_expression_value;
     [apply old_expression_value;apply value_temp;exact ARGV|apply old_expression_value;apply value_int|apply argument_pointer_add;lia].
   + reflexivity.
   + eapply assign_loc_value;[reflexivity|exact STORE].
 - eapply store_next;[right;reflexivity|apply unchanged_store_edge;WriteAll.structural|].
   constructor;right;reflexivity.
Qed.
Theorem arguments_pointer_certificate cell e le before k argv ofs :
 e!_policy__1=None->le!_argv=Some(Vptr argv ofs)->Mem.valid_access before Mptr main_policy_block 88 Writable->
 exists after,Mem.store Mptr before main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 region_certificate main_ge cell(flag_memory before after)(flag_frontier after(validation_suffix 22)k e le)3
 (State f_main(validation_suffix 21)k e le before).
Proof.
 intros GLOBAL ARGV WRITE.
 destruct(Mem.valid_access_store before Mptr main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))WRITE)as[after STORE].
 exists after;split;[exact STORE|];change 3 with(3+0);eapply region_store_path.
 - eapply arguments_pointer_path with(argv:=argv)(ofs:=ofs);eassumption.
 - apply region_stop;[right;reflexivity|exists le;split;[split;reflexivity|reflexivity]].
Qed.
Theorem pointer_store_load before after b ofs pointer : Mem.store Mptr before b ofs pointer=Some after->
 (exists block pos,pointer=Vptr block pos)->Mem.load Mptr after b ofs=Some pointer.
Proof. intros STORE[block[pos EQ]];subst pointer;rewrite(Mem.load_store_same _ _ _ _ _ _ STORE);reflexivity. Qed.
