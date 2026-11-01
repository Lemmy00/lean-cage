(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import StringMachine ArgumentMemory ArgumentBounds.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish
 ValidationAllocation ExecutableCaller ValidationComposition.
From LeanCageInitialization Require Import AssemblyRegions FlagStores PointerStores StoreFrames.
Import ListNotations.
Open Scope nat_scope.
Lemma executable_bounds_frame e le mid k m argc x rest values s : validation_frame le mid->
 executable_bounds_frontier e mid k m argc x rest values s->executable_bounds_frontier e le k m argc x rest values s.
Proof.
 intros FRAME END;unfold executable_bounds_frontier in *;destruct(executable_bad(guest_bytes x));[|exact END].
 destruct END as[final[MORE LAST]];exists final;split;[eapply validation_frame_trans;eassumption|exact LAST].
Qed.
Theorem arguments_initialization_certificate cell e le before k argc argv ofs x rest values :
 (17<=argc<=2147483647)%Z->(16+Z.of_nat(length(x::rest))=argc)%Z->guest_table_span ofs argc->
 guest_arguments_owned before argv ofs 16(x::rest)->setup_separate argv->
 Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))(x::rest)->
 policy_image before values->literals_owned before->
 e!_strcmp=None->e!_strlen=None->e!_policy__1=None->e!___stringlit_135=None->e!___stringlit_134=None->
 le!_argv=Some(Vptr argv ofs)->le!_argc=Some(Vint(Int.repr argc))->
 Mem.valid_access before Mptr main_policy_block 88 Writable->
 exists after,Mem.store Mptr before main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 region_certificate main_ge cell(flag_memory before after)(executable_bounds_frontier e le k after argc x rest values)
 (26*length(x::rest)+191)(State f_main(validation_suffix 21)k e le before).
Proof.
 intros COUNT SIZE SPAN OWN ARGVSEP STRINGSEP IMAGE LITERALS STRCMP STRLEN POLICY SHELL PYTHON ARGV ARGC WRITE.
 destruct(arguments_pointer_certificate cell e le before k argv ofs POLICY ARGV WRITE)as[after[STORE CERT]].
 assert(FRAME:setup_frame before after)by(eapply setup_store_frame;[|exact STORE];unfold setup_cell;auto 8).
 assert(OWN':guest_arguments_owned after argv ofs 16(x::rest))by(eapply setup_guest_arguments;eassumption).
 assert(IMAGE':policy_image after values)by(eapply setup_policy_image;eassumption).
 assert(LITERALS':literals_owned after)by(eapply setup_literals;eassumption).
 assert(LOAD:Mem.loadv Mptr after(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))).
 { change(Mem.load Mptr after main_policy_block 88=Some(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))).
   rewrite(Mem.load_store_same _ _ _ _ _ _ STORE);reflexivity. }
 exists after;split;[exact STORE|].
 replace(26*length(x::rest)+191)with(3+(34+(26*length(x::rest)+154)))by lia.
 eapply region_bind;[exact CERT|].
 intros endpoint[mid[REGS END]];subst endpoint.
 eapply region_convert.
 - eapply executable_bounds_certificate;[exact COUNT|exact SIZE|exact SPAN|exact OWN'|exact IMAGE'|exact STRCMP|exact STRLEN|exact POLICY|exact SHELL|exact PYTHON|
    rewrite(proj1 REGS);exact ARGV|rewrite(proj2 REGS);exact ARGC|exact LOAD|owned_literal|owned_literal].
 - intros current EQ;right;exact EQ.
 - intros last RESULT;eapply executable_bounds_frame;[exact REGS|exact RESULT].
Qed.
