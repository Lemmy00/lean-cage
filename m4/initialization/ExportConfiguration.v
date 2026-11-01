(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish ExportCaller.
From LeanCageInitialization Require Import AssemblyRegions FlagStores StoreFrames ConfigurationMemory ConfigurationSource.
Import ListNotations.
Open Scope nat_scope.
Definition export_configuration_frontier before configured e le k bytes s :=
 if export_bad bytes then selection_frontier 16 e le k before true s
 else flag_frontier configured(validation_suffix 20)k e le s.
Theorem export_configuration_certificate cell e le before k argv ofs export tree stdin bytes :
 e!_strcmp=None->e!___stringlit_133=None->e!___stringlit_132=None->e!_policy__1=None->
 e!_tree_digest=None->e!_stdin_digest=None->le!_argv=Some(Vptr argv ofs)->setup_separate argv->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value export)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin)->
 c_string before export bytes->c_string before(literal_address ___stringlit_133)discard_bytes->
 c_string before(literal_address ___stringlit_132)files_bytes->
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 Mem.valid_access before Mptr(symbol_block _tree_digest)0 Writable->
 Mem.valid_access before Mptr(symbol_block _stdin_digest)0 Writable->
 exists flagged tree_set configured,configuration_stores before flagged tree_set configured(bytes_equal bytes files_bytes)tree stdin /\
 region_certificate main_ge cell(configuration_prefix before flagged tree_set configured)
 (export_configuration_frontier before configured e le k bytes)49(State f_main(validation_suffix 16)k e le before).
Proof.
 intros STRCMP DISCARD FILES POLICY TREE STDIN ARGV SEP EL TL SL OWN D F FW TW SW.
 destruct(configuration_exists before(bytes_equal bytes files_bytes)tree stdin FW TW SW)as[flagged[tree_set[configured STORES]]].
 exists flagged,tree_set,configured;split;[exact STORES|].
 change 49 with(26+23);eapply region_bind with(R:=selection_frontier 16 e le k before(export_bad bytes)).
 - eapply region_convert.
   + eapply export_check_certificate;[exact STRCMP|exact DISCARD|exact FILES|exact ARGV|exact EL|exact OWN|exact D|exact F].
   + unfold configuration_prefix;intros;tauto.
   + intros;assumption.
 - intros endpoint[mid[FRAME END]];unfold export_configuration_frontier;destruct(export_bad bytes)eqn:BAD.
   + apply region_stop;[rewrite END;left;reflexivity|exists mid;auto].
   + subst endpoint;change(selection_after 16)with(validation_suffix 17).
     destruct(configuration_certificate cell e mid before k argv ofs export tree stdin bytes STRCMP FILES POLICY TREE STDIN
      ltac:(rewrite(proj1 FRAME);exact ARGV)SEP EL TL SL OWN F FW TW SW)
      as[f2[t2[s2[STORES2 CERT]]]].
     assert(f2=flagged /\t2=tree_set /\s2=configured)as[E1[E2 E3]].
     { destruct STORES as[A[B C]];destruct STORES2 as[D2[E F2]];split;[congruence|];
       assert(f2=flagged)by congruence;subst f2;split;[congruence|];assert(t2=tree_set)by congruence;subst t2;congruence. }
     subst f2 t2 s2;eapply region_convert;[exact CERT|intros;assumption|].
     intros last[final[MORE LAST]];exists final;split;[eapply validation_frame_trans;eassumption|exact LAST].
Qed.
