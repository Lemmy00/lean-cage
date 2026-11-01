(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import StringMachine ArgumentMemory.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish
 ValidationAllocation DigestCaller ExportCaller ValidationComposition.
From LeanCageInitialization Require Import AssemblyRegions FlagStores StoreFrames ConfigurationMemory ExportConfiguration
 ArgumentsInitialization DigestArguments.
Import ListNotations.
Open Scope nat_scope.
Lemma digest_arguments_frame before after e le mid k argc tree_bytes stdin_bytes x rest values s :
 validation_frame le mid->digest_arguments_frontier before after e mid k argc tree_bytes stdin_bytes x rest values s->
 digest_arguments_frontier before after e le k argc tree_bytes stdin_bytes x rest values s.
Proof.
 intros FRAME END;unfold digest_arguments_frontier in *;destruct(digest_pair_bad tree_bytes stdin_bytes).
 - destruct END as[final[MORE LAST]];exists final;split;[eapply validation_frame_trans;eassumption|exact LAST].
 - eapply executable_bounds_frame;eassumption.
Qed.
Definition initialization_frontier before configured after e le k argc export_bytes tree_bytes stdin_bytes x rest values s :=
 if export_bad export_bytes then selection_frontier 16 e le k before true s
 else digest_arguments_frontier configured after e le k argc tree_bytes stdin_bytes x rest values s.
Definition initialization_prefix before flagged tree_set configured after current :=
 configuration_prefix before flagged tree_set configured current \/current=after.
Theorem initialization_certificate cell e le before k argc argv ofs export tree stdin export_bytes tree_bytes stdin_bytes x rest values :
 (17<=argc<=2147483647)%Z->(16+Z.of_nat(length(x::rest))=argc)%Z->guest_table_span ofs argc->
 guest_arguments_owned before argv ofs 16(x::rest)->setup_separate argv->
 Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))(x::rest)->
 setup_separate(address_block tree)->setup_separate(address_block stdin)->
 policy_image before values->literals_owned before->
 e!_strcmp=None->e!_strlen=None->e!_policy__1=None->e!___stringlit_133=None->e!___stringlit_132=None->
 e!___stringlit_135=None->e!___stringlit_134=None->e!___stringlit_56=None->
 e!_tree_digest=None->e!_stdin_digest=None->e!_digest_text=None->
 le!_argv=Some(Vptr argv ofs)->le!_argc=Some(Vint(Int.repr argc))->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value export)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin)->
 c_string before export export_bytes->c_string before tree tree_bytes->c_string before stdin stdin_bytes->
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 Mem.valid_access before Mptr(symbol_block _tree_digest)0 Writable->
 Mem.valid_access before Mptr(symbol_block _stdin_digest)0 Writable->
 Mem.valid_access before Mptr main_policy_block 88 Writable->
 exists flagged tree_set configured after,
 configuration_stores before flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 region_certificate main_ge cell(initialization_prefix before flagged tree_set configured after)
 (initialization_frontier before configured after e le k argc export_bytes tree_bytes stdin_bytes x rest values)
 (26*length(x::rest)+4540)(State f_main(validation_suffix 16)k e le before).
Proof.
 intros COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW.
 destruct(export_configuration_certificate cell e le before k argv ofs export tree stdin export_bytes
 STRCMP DISCARD FILES POLICY TREE STDIN ARGV ARGVSEP EL TL SL EO ltac:(owned_literal)ltac:(owned_literal)FW TW SW)
 as[flagged[tree_set[configured[STORES CERT]]]].
 pose proof(configuration_frames _ _ _ _ _ _ _ STORES)as[F[T FRAME]].
 assert(AW':Mem.valid_access configured Mptr main_policy_block 88 Writable)by(eapply setup_access;eassumption).
 destruct(Mem.valid_access_store configured Mptr main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))AW')as[after STORE].
 exists flagged,tree_set,configured,after;split;[exact STORES|];split;[exact STORE|].
 replace(26*length(x::rest)+4540)with(49+(26*length(x::rest)+4491))by lia.
 eapply region_bind with(R:=export_configuration_frontier before configured e le k export_bytes).
 - eapply region_convert;[exact CERT|unfold initialization_prefix;intros;auto|intros;assumption].
 - intros endpoint END;unfold export_configuration_frontier in END;unfold initialization_frontier;
   destruct(export_bad export_bytes)eqn:BAD.
   + destruct END as[mid[REGS STATE]];apply region_stop;[rewrite STATE;left;left;reflexivity|exists mid;auto].
   + destruct END as[mid[REGS STATE]];subst endpoint.
     assert(OWN':guest_arguments_owned configured argv ofs 16(x::rest))by(eapply setup_guest_arguments;eassumption).
     assert(IMAGE':policy_image configured values)by(eapply setup_policy_image;eassumption).
     assert(LITERALS':literals_owned configured)by(eapply setup_literals;eassumption).
     assert(TO':c_string configured tree tree_bytes)by(eapply setup_string;eassumption).
     assert(SO':c_string configured stdin stdin_bytes)by(eapply setup_string;eassumption).
     destruct(configuration_loads _ _ _ _ _ _ _ STORES)as[FLAGLOAD[TREELOAD STDINLOAD]].
     assert(TL':Mem.loadv Mptr configured(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value tree))by exact TREELOAD.
     assert(SL':Mem.loadv Mptr configured(Vptr(symbol_block _stdin_digest)Ptrofs.zero)=Some(address_value stdin))by exact STDINLOAD.
     destruct(digest_arguments_certificate cell e mid configured k argc argv ofs tree stdin tree_bytes stdin_bytes x rest values
      COUNT SIZE SPAN OWN' ARGVSEP STRINGSEP IMAGE' LITERALS' STRCMP STRLEN POLICY SHELL PYTHON NONE TREE STDIN DIGEST
      ltac:(rewrite(proj1 REGS);exact ARGV)ltac:(rewrite(proj2 REGS);exact ARGC)TL' SL' TO' SO' AW')as[other[STORE2 TAIL]].
     assert(other=after)by congruence;subst other.
     eapply region_convert;[exact TAIL| |].
     * unfold flag_memory,initialization_prefix,configuration_prefix;intros;tauto.
     * intros last RESULT;eapply digest_arguments_frame;[exact REGS|exact RESULT].
Qed.
Theorem initialization_prefix_frame before flagged tree_set configured after current export_flag tree stdin argv ofs :
 configuration_stores before flagged tree_set configured export_flag tree stdin->
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after->
 initialization_prefix before flagged tree_set configured after current->setup_frame before current.
Proof.
 intros STORES STORE[PRIOR|EQ].
 - eapply configuration_prefix_frame;eassumption.
 - subst current;destruct(configuration_frames _ _ _ _ _ _ _ STORES)as[F[T FRAME]].
   eapply setup_frame_trans;[exact FRAME|];eapply setup_store_frame;[|exact STORE];unfold setup_cell;auto 8.
Qed.
From LeanCageValidation Require Import StringSource.

Theorem initialization_source cell e le before k argc argv ofs export tree stdin export_bytes tree_bytes stdin_bytes x rest values :
 (17<=argc<=2147483647)%Z->(16+Z.of_nat(length(x::rest))=argc)%Z->guest_table_span ofs argc->
 guest_arguments_owned before argv ofs 16(x::rest)->setup_separate argv->
 Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))(x::rest)->
 setup_separate(address_block tree)->setup_separate(address_block stdin)->
 policy_image before values->literals_owned before->
 e!_strcmp=None->e!_strlen=None->e!_policy__1=None->e!___stringlit_133=None->e!___stringlit_132=None->
 e!___stringlit_135=None->e!___stringlit_134=None->e!___stringlit_56=None->
 e!_tree_digest=None->e!_stdin_digest=None->e!_digest_text=None->
 le!_argv=Some(Vptr argv ofs)->le!_argc=Some(Vint(Int.repr argc))->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value export)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin)->
 c_string before export export_bytes->c_string before tree tree_bytes->c_string before stdin stdin_bytes->
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 Mem.valid_access before Mptr(symbol_block _tree_digest)0 Writable->
 Mem.valid_access before Mptr(symbol_block _stdin_digest)0 Writable->
 Mem.valid_access before Mptr main_policy_block 88 Writable->
 exists flagged tree_set configured after,
 configuration_stores before flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 region_guarantee main_ge cell(initialization_prefix before flagged tree_set configured after)
 (initialization_frontier before configured after e le k argc export_bytes tree_bytes stdin_bytes x rest values)
 (26*length(x::rest)+4540)(State f_main(validation_suffix 16)k e le before).
Proof.
 intros COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW.
 destruct(initialization_certificate cell e le before k argc argv ofs export tree stdin export_bytes tree_bytes stdin_bytes x rest values
 COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW)
 as[flagged[tree_set[configured[after[STORES[STORE CERT]]]]]].
 exists flagged,tree_set,configured,after;split;[exact STORES|];split;[exact STORE|apply region_guaranteed;exact CERT].
Qed.
