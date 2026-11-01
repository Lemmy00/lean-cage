(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues.
From LeanCageInitialization Require Import FlagStores PointerStores StoreFrames ConfigurationMemory.
Import ListNotations.
Open Scope nat_scope.
Lemma string_cost_append left right : string_cost(left++right)=string_cost left+string_cost right.
Proof. unfold string_cost;rewrite filter_app,length_app;reflexivity. Qed.
Lemma loss_after_execution ge cell start events endpoint : string_steps ge cell(live start)events(live endpoint)->
 string_steps ge cell(live start)(events++[string_loss])(dead(memory_of endpoint)).
Proof. intros RUN;eapply string_steps_trans;[exact RUN|];econstructor;[apply string_loss_everywhere|constructor]. Qed.
Theorem configuration_stages cell e le before k argv ofs export tree stdin bytes :
 e!_strcmp=None->e!___stringlit_132=None->e!_policy__1=None->e!_tree_digest=None->e!_stdin_digest=None->
 le!_argv=Some(Vptr argv ofs)->setup_separate argv->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value export)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin)->
 c_string before export bytes->c_string before(literal_address ___stringlit_132)files_bytes->
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 Mem.valid_access before Mptr(symbol_block _tree_digest)0 Writable->
 Mem.valid_access before Mptr(symbol_block _stdin_digest)0 Writable->
 exists flagged tree_set configured,
 configuration_stores before flagged tree_set configured(bytes_equal bytes files_bytes)tree stdin /\
 forall current,In current[before;flagged;tree_set;configured]->exists events endpoint,
 string_steps main_ge cell(live(State f_main(validation_suffix 17)k e le before))events(live endpoint) /\
 memory_of endpoint=current /\string_cost events<=23 /\
 string_steps main_ge cell(live(State f_main(validation_suffix 17)k e le before))(events++[string_loss])(dead current).
Proof.
 intros STRCMP FILES POLICY TREE STDIN ARGV SEP EL TL SL OWN TEXT FW TW SW.
 destruct(export_flag_certificate cell e le before k argv ofs export bytes STRCMP FILES POLICY ARGV EL OWN TEXT FW)
 as[flagged[FLAG C1]].
 assert(F:setup_frame before flagged)by(eapply setup_store_frame;[|exact FLAG];unfold setup_cell;auto 8).
 destruct(region_actual _ _ _ _ _ _ C1)as[es1[ss1[R1[B1[M1[l1[REG1 END1]]]]]]];subst ss1.
 assert(TL':Mem.loadv Mptr flagged(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree))by(eapply setup_load;eassumption).
 assert(TW':Mem.valid_access flagged Mptr(symbol_block _tree_digest)0 Writable)by(eapply setup_access;eassumption).
 destruct(digest_pointer_certificate cell e l1 flagged k 18 _t'284 14 _tree_digest argv ofs tree
 (or_introl eq_refl)(proj1 pointer_statements_actual)ltac:(discriminate)ltac:(discriminate)ltac:(lia)
 ltac:(rewrite(proj1 REG1);exact ARGV)TREE(or_introl eq_refl)TL' TW')as[tree_set[TREESTORE C2]].
 assert(T:setup_frame flagged tree_set)by(eapply setup_store_frame;[|exact TREESTORE];unfold setup_cell;auto 8).
 assert(FT:setup_frame before tree_set)by(eapply setup_frame_trans;eassumption).
 destruct(region_actual _ _ _ _ _ _ C2)as[es2[ss2[R2[B2[M2[l2[REG2 END2]]]]]]];subst ss2.
 assert(SL':Mem.loadv Mptr tree_set(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin))by(eapply setup_load;eassumption).
 assert(SW':Mem.valid_access tree_set Mptr(symbol_block _stdin_digest)0 Writable)by(eapply setup_access;eassumption).
 destruct(digest_pointer_certificate cell e l2 tree_set k 19 _t'283 15 _stdin_digest argv ofs stdin
 (or_intror eq_refl)(proj2 pointer_statements_actual)ltac:(discriminate)ltac:(discriminate)ltac:(lia)
 ltac:(rewrite(proj1 REG2),(proj1 REG1);exact ARGV)STDIN(or_intror(or_introl eq_refl))SL' SW')as[configured[STDINSTORE C3]].
 destruct(region_actual _ _ _ _ _ _ C3)as[es3[ss3[R3[B3[M3[l3[REG3 END3]]]]]]];subst ss3.
 assert(R12:string_steps main_ge cell(live(State f_main(validation_suffix 17)k e le before))(es1++es2)
 (live(State f_main(validation_suffix 19)k e l2 tree_set)))by(eapply string_steps_trans;eassumption).
 assert(R123:string_steps main_ge cell(live(State f_main(validation_suffix 17)k e le before))((es1++es2)++es3)
 (live(State f_main(validation_suffix 20)k e l3 configured)))by(eapply string_steps_trans;eassumption).
 exists flagged,tree_set,configured;split;[split;[exact FLAG|];split;assumption|].
 intros current[<-|[<-|[<-|[<-|IMP]]]];[| | | |contradiction].
 - exists [],(State f_main(validation_suffix 17)k e le before);split;[constructor|];split;[reflexivity|];split;[cbn;lia|].
   econstructor;[apply string_loss_everywhere|constructor].
 - exists es1,(State f_main(validation_suffix 18)k e l1 flagged);split;[exact R1|];split;[reflexivity|];split;[lia|exact(loss_after_execution _ _ _ _ _ R1)].
 - exists(es1++es2),(State f_main(validation_suffix 19)k e l2 tree_set);split;[exact R12|];split;[reflexivity|];split;[rewrite string_cost_append;lia|exact(loss_after_execution _ _ _ _ _ R12)].
 - exists((es1++es2)++es3),(State f_main(validation_suffix 20)k e l3 configured);split;[exact R123|];split;[reflexivity|];split;[rewrite !string_cost_append;lia|exact(loss_after_execution _ _ _ _ _ R123)].
Qed.
