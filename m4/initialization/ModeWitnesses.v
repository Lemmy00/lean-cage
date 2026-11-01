(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine Library FreshMemoryDraft WriteAll.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath ArgumentWitnesses.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import StringRegion StringSource ValidationStructure ValidationValues
 ValidationAllocation ValidationWitnesses ValidationSamples.
From LeanCageInitialization Require Import FlagStores ModeInitialization InitializationAllocation.
Import ListNotations.
Open Scope Z_scope.
Theorem mode_initialization_source cell e le before k argc argv ofs p bytes :
 (Int.min_signed<=argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr argc))->
 e!_strcmp=None->e!___stringlit_131=None->e!___stringlit_130=None->e!_preflight=None->
 le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string before p bytes->c_string before(literal_address ___stringlit_131)plan_bytes->
 c_string before(literal_address ___stringlit_130)check_bytes->
 Mem.valid_access before Mint32(symbol_block _preflight)0 Writable->
 exists after,Mem.store Mint32 before(symbol_block _preflight)0(Val.of_bool(bytes_equal bytes check_bytes))=Some after /\
 region_guarantee main_ge cell(flag_memory before after)(mode_initialization_frontier before after e le k argc bytes)42
 (State f_main(validation_suffix 2)k e le before).
Proof.
 intros RANGE ARGC STRCMP PLAN CHECK GLOBAL ARGV LOAD OWN P C WRITE.
 destruct(mode_initialization_certificate cell e le before k argc argv ofs p bytes
 RANGE ARGC STRCMP PLAN CHECK GLOBAL ARGV LOAD OWN P C WRITE)as[after[STORE CERT]].
 exists after;split;[exact STORE|apply region_guaranteed;exact CERT].
Qed.
Theorem allocated_mode_initialization cell argc bytes : Int.min_signed<=argc<=Int.max_signed->digest_input_admissible bytes->
 exists initial before after argv events endpoint,Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 Mem.store Mint32 before(symbol_block _preflight)0(Val.of_bool(bytes_equal bytes check_bytes))=Some after /\
 string_steps main_ge cell(live(State f_main(validation_suffix 2)Kstop empty_env(argument_witness_env argv argc)before))events(live endpoint) /\
 (string_cost events<=42)%nat /\mode_initialization_frontier before after empty_env(argument_witness_env argv argc)Kstop argc bytes endpoint.
Proof.
 intros RANGE VALID;destruct(allocated_validation_input 1 bytes ltac:(lia)VALID)
 as[initial[before[argv[p[INIT[OLD[OWN[LITERALS[LOAD[FRESH TABLE]]]]]]]]]].
 pose proof(setup_writable_old initial before OLD(setup_initial_writable initial INIT))as[WRITE REST].
 destruct(mode_initialization_certificate cell empty_env(argument_witness_env argv argc)before Kstop argc argv Ptrofs.zero p bytes
 RANGE ltac:(unfold argument_witness_env;WriteAll.lookup)eq_refl eq_refl eq_refl eq_refl
 ltac:(unfold argument_witness_env;WriteAll.lookup)ltac:(rewrite Ptrofs.add_zero_l;exact LOAD)OWN
 ltac:(owned_literal)ltac:(owned_literal)WRITE)as[after[STORE CERT]].
 destruct(region_actual _ _ _ _ _ _ CERT)as[events[endpoint[RUN[BOUND[MEM END]]]]].
 exists initial,before,after,argv,events,endpoint;auto 12.
Qed.
Theorem mode_initialization_samples cell c : In c mode_cases->
 exists initial before after argv events endpoint,Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 Mem.store Mint32 before(symbol_block _preflight)0(Val.of_bool(bytes_equal(mode_text c)check_bytes))=Some after /\
 string_steps main_ge cell(live(State f_main(validation_suffix 2)Kstop empty_env(argument_witness_env argv(mode_count c))before))events(live endpoint) /\
 (string_cost events<=42)%nat /\mode_initialization_frontier before after empty_env(argument_witness_env argv(mode_count c))Kstop(mode_count c)(mode_text c)endpoint.
Proof.
 intros IN;pose proof mode_cases_checked as VALID;rewrite Forall_forall in VALID;
 destruct(VALID c IN)as[LOW[HIGH[OWN RESULT]]];apply Z.leb_le in LOW,HIGH.
 apply allocated_mode_initialization;[lia|apply digest_input_admissible_sound;exact OWN].
Qed.
