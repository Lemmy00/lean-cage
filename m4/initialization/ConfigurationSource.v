(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish.
From LeanCageInitialization Require Import AssemblyRegions FlagStores PointerStores StoreFrames ConfigurationMemory.
Import ListNotations.
Open Scope nat_scope.
Theorem configuration_certificate cell e le before k argv ofs export tree stdin bytes :
 e!_strcmp=None->e!___stringlit_132=None->e!_policy__1=None->e!_tree_digest=None->e!_stdin_digest=None->
 le!_argv=Some(Vptr argv ofs)->setup_separate argv->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value export)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin)->
 c_string before export bytes->c_string before(literal_address ___stringlit_132)files_bytes->
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 Mem.valid_access before Mptr(symbol_block _tree_digest)0 Writable->
 Mem.valid_access before Mptr(symbol_block _stdin_digest)0 Writable->
 exists flagged tree_set configured,configuration_stores before flagged tree_set configured(bytes_equal bytes files_bytes)tree stdin /\
 region_certificate main_ge cell(configuration_prefix before flagged tree_set configured)
 (flag_frontier configured(validation_suffix 20)k e le)23(State f_main(validation_suffix 17)k e le before).
Proof.
 intros STRCMP LITERAL POLICY TREE STDIN ARGV SEP EL TL SL OWN TEXT FW TW SW.
 destruct(configuration_exists before(bytes_equal bytes files_bytes)tree stdin FW TW SW)
 as[flagged[tree_set[configured STORES]]].
 pose proof(configuration_frames _ _ _ _ _ _ _ STORES)as[F[T S]].
 pose proof STORES as[FLAGSTORE[TREESTORE STDINSTORE]].
 exists flagged,tree_set,configured;split;[exact STORES|].
 change 23 with(11+12);eapply region_bind with(R:=flag_frontier flagged(validation_suffix 18)k e le).
 - destruct(export_flag_certificate cell e le before k argv ofs export bytes STRCMP LITERAL POLICY ARGV EL OWN TEXT FW)
   as[other[STORE CERT]];assert(other=flagged)by congruence;subst other.
   eapply region_convert;[exact CERT|unfold flag_memory,configuration_prefix;intros;tauto|intros;assumption].
 - intros endpoint[mid[FRAME END]];subst endpoint.
   change 12 with(6+6);eapply region_bind with(R:=flag_frontier tree_set(validation_suffix 19)k e le).
   + assert(TL':Mem.loadv Mptr flagged(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree))
      by(eapply setup_load;[exact F|exact SEP|exact TL]).
     assert(TW':Mem.valid_access flagged Mptr(symbol_block _tree_digest)0 Writable)by(eapply setup_access;eassumption).
     destruct(digest_pointer_certificate cell e mid flagged k 18 _t'284 14 _tree_digest argv ofs tree
       (or_introl eq_refl)(proj1 pointer_statements_actual)ltac:(discriminate)ltac:(discriminate)ltac:(lia)
       ltac:(rewrite(proj1 FRAME);exact ARGV)TREE(or_introl eq_refl)TL' TW')as[other[STORE CERT]].
     assert(other=tree_set)by congruence;subst other.
     eapply region_convert;[exact CERT|unfold flag_memory,configuration_prefix;intros;tauto|].
     intros last[final[MORE LAST]];exists final;split;[eapply validation_frame_trans;eassumption|exact LAST].
   + intros endpoint[mid2[FRAME2 END2]];subst endpoint.
     assert(SL':Mem.loadv Mptr tree_set(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin))
      by(eapply setup_load;[exact T|exact SEP|exact SL]).
     assert(SW':Mem.valid_access tree_set Mptr(symbol_block _stdin_digest)0 Writable)by(eapply setup_access;eassumption).
     destruct(digest_pointer_certificate cell e mid2 tree_set k 19 _t'283 15 _stdin_digest argv ofs stdin
       (or_intror eq_refl)(proj2 pointer_statements_actual)ltac:(discriminate)ltac:(discriminate)ltac:(lia)
       ltac:(rewrite(proj1 FRAME2);exact ARGV)STDIN(or_intror(or_introl eq_refl))SL' SW')as[other[STORE CERT]].
     assert(other=configured)by congruence;subst other.
     eapply region_convert;[exact CERT|unfold flag_memory,configuration_prefix;intros;tauto|].
     intros last[final[MORE LAST]];exists final;split;[eapply validation_frame_trans;eassumption|exact LAST].
Qed.
