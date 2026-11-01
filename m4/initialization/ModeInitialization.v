(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish ModeCaller.
From LeanCageInitialization Require Import AssemblyRegions FlagStores.
Import ListNotations.
Open Scope nat_scope.
Definition mode_initialization_frontier before after e le k argc bytes s :=
 if mode_bad argc bytes then selection_frontier 2 e le k before true s
 else flag_frontier after(validation_suffix 4)k e le s.
Theorem mode_initialization_certificate cell e le before k argc argv ofs p bytes :
 (Int.min_signed<=argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr argc))->
 e!_strcmp=None->e!___stringlit_131=None->e!___stringlit_130=None->e!_preflight=None->
 le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string before p bytes->c_string before(literal_address ___stringlit_131)plan_bytes->
 c_string before(literal_address ___stringlit_130)check_bytes->
 Mem.valid_access before Mint32(symbol_block _preflight)0 Writable->
 exists after,Mem.store Mint32 before(symbol_block _preflight)0(Val.of_bool(bytes_equal bytes check_bytes))=Some after /\
 region_certificate main_ge cell(flag_memory before after)(mode_initialization_frontier before after e le k argc bytes)42
 (State f_main(validation_suffix 2)k e le before).
Proof.
 intros RANGE ARGC STRCMP PLAN CHECK GLOBAL ARGV LOAD OWN P C WRITE.
 destruct(Mem.valid_access_store before Mint32(symbol_block _preflight)0(Val.of_bool(bytes_equal bytes check_bytes))WRITE)as[after STORE].
 exists after;split;[exact STORE|].
 change 42 with(31+11);eapply region_bind with(R:=selection_frontier 2 e le k before(mode_bad argc bytes)).
 - eapply region_convert.
   + eapply mode_check_certificate;[exact RANGE|exact ARGC|exact STRCMP|exact PLAN|exact CHECK|exact ARGV|exact LOAD|exact OWN|exact P|exact C].
   + intros current EQ;left;exact EQ.
   + intros;assumption.
 - intros endpoint[intermediate[FRAME END]].
   unfold mode_initialization_frontier;destruct(mode_bad argc bytes)eqn:BAD.
   + apply region_stop;[rewrite END;left;reflexivity|exists intermediate;auto].
   + subst endpoint;change(selection_after 2)with(validation_suffix 3).
     destruct(preflight_certificate cell e intermediate before k argv ofs p bytes STRCMP CHECK GLOBAL
      ltac:(rewrite(proj1 FRAME);exact ARGV)LOAD OWN C WRITE)as[stored[STORE2 CERT]].
     assert(stored=after)by congruence;subst stored.
     eapply region_convert;[exact CERT|intros;assumption|].
     intros last[final[MORE LAST]];exists final;split;[eapply validation_frame_trans;eassumption|exact LAST].
Qed.
