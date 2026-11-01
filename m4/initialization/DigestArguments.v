(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import StringMachine ArgumentMemory.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish
 ValidationAllocation DigestCaller ValidationComposition.
From LeanCageInitialization Require Import AssemblyRegions FlagStores StoreFrames ArgumentsInitialization.
Import ListNotations.
Open Scope nat_scope.
Definition digest_arguments_frontier before after e le k argc tree_bytes stdin_bytes x rest values s :=
 if digest_pair_bad tree_bytes stdin_bytes then selection_frontier 20 e le k before true s
 else executable_bounds_frontier e le k after argc x rest values s.
Theorem digest_arguments_certificate cell e le before k argc argv ofs tree stdin tree_bytes stdin_bytes x rest values :
 (17<=argc<=2147483647)%Z->(16+Z.of_nat(length(x::rest))=argc)%Z->guest_table_span ofs argc->
 guest_arguments_owned before argv ofs 16(x::rest)->setup_separate argv->
 Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))(x::rest)->policy_image before values->literals_owned before->
 e!_strcmp=None->e!_strlen=None->e!_policy__1=None->e!___stringlit_135=None->e!___stringlit_134=None->
 e!___stringlit_56=None->e!_tree_digest=None->e!_stdin_digest=None->e!_digest_text=None->
 le!_argv=Some(Vptr argv ofs)->le!_argc=Some(Vint(Int.repr argc))->
 Mem.loadv Mptr before(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value tree)->
 Mem.loadv Mptr before(Vptr(symbol_block _stdin_digest)Ptrofs.zero)=Some(address_value stdin)->
 c_string before tree tree_bytes->c_string before stdin stdin_bytes->
 Mem.valid_access before Mptr main_policy_block 88 Writable->
 exists after,Mem.store Mptr before main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 region_certificate main_ge cell(flag_memory before after)
 (digest_arguments_frontier before after e le k argc tree_bytes stdin_bytes x rest values)
 (26*length(x::rest)+4491)(State f_main(validation_suffix 20)k e le before).
Proof.
 intros COUNT SIZE SPAN OWN ARGVSEP STRINGSEP IMAGE LITERALS STRCMP STRLEN POLICY SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC TL SL TO SO WRITE.
 destruct(Mem.valid_access_store before Mptr main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))WRITE)as[after STORE].
 exists after;split;[exact STORE|].
 replace(26*length(x::rest)+4491)with(4300+(26*length(x::rest)+191))by lia.
 eapply region_bind with(R:=selection_frontier 20 e le k before(digest_pair_bad tree_bytes stdin_bytes)).
 - eapply region_convert.
   + eapply digest_pair_certificate;[exact STRCMP|exact NONE|exact TREE|exact STDIN|exact DIGEST|exact TL|exact SL|exact TO|exact SO|owned_literal].
   + intros current EQ;left;exact EQ.
   + intros;assumption.
 - intros endpoint[mid[FRAME END]];unfold digest_arguments_frontier;destruct(digest_pair_bad tree_bytes stdin_bytes)eqn:BAD.
   + apply region_stop;[rewrite END;left;reflexivity|exists mid;auto].
   + subst endpoint;change(selection_after 20)with(validation_suffix 21).
     destruct(arguments_initialization_certificate cell e mid before k argc argv ofs x rest values
      COUNT SIZE SPAN OWN ARGVSEP STRINGSEP IMAGE LITERALS STRCMP STRLEN POLICY SHELL PYTHON
      ltac:(rewrite(proj1 FRAME);exact ARGV)ltac:(rewrite(proj2 FRAME);exact ARGC)WRITE)as[other[STORE2 CERT]].
     assert(other=after)by congruence;subst other;eapply region_convert;[exact CERT|intros;assumption|].
     intros last RESULT;eapply executable_bounds_frame;[exact FRAME|exact RESULT].
Qed.
