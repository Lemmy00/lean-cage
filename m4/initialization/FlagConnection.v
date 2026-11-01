(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From LeanImport Require Import Lean.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
Require Import Library Machine.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import StringRegion StringSource ValidationStructure ValidationValues
 ValidationImport StringImported StringConnection.
From LeanCageInitialization Require Import FlagStores.
Local Close Scope lean_scope.
Import ListNotations.
Open Scope nat_scope.
Definition imported_preflight_flag xs := validation_bool(LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_checkBytes).
Definition imported_export_flag xs := validation_bool(LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_filesBytes).
Theorem imported_preflight_flag_agreement xs bytes : validation_values xs=map Byte.unsigned bytes->
 imported_preflight_flag xs=bytes_equal bytes check_bytes.
Proof.
 intros REPR;unfold imported_preflight_flag;rewrite validation_imported_equal,REPR.
 change(validation_values LeanCageM4_Validation_checkBytes)with(map Byte.unsigned check_bytes).
 apply signed_list_eq_bytes.
Qed.
Theorem imported_export_flag_agreement xs bytes : validation_values xs=map Byte.unsigned bytes->
 imported_export_flag xs=bytes_equal bytes files_bytes.
Proof.
 intros REPR;unfold imported_export_flag;rewrite validation_imported_equal,REPR.
 change(validation_values LeanCageM4_Validation_filesBytes)with(map Byte.unsigned files_bytes).
 apply signed_list_eq_bytes.
Qed.
Theorem imported_preflight_source cell e le before k argv ofs p xs bytes :
 validation_values xs=map Byte.unsigned bytes->
 e!_strcmp=None->e!___stringlit_130=None->e!_preflight=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string before p bytes->c_string before(literal_address ___stringlit_130)check_bytes->
 Mem.valid_access before Mint32(symbol_block _preflight)0 Writable->
 exists after,Mem.store Mint32 before(symbol_block _preflight)0(Val.of_bool(imported_preflight_flag xs))=Some after /\
 region_guarantee main_ge cell(flag_memory before after)(flag_frontier after(selection_after 3)k e le)11
 (State f_main(validation_suffix 3)k e le before).
Proof.
 intros REPR STRCMP CHECK GLOBAL ARGV LOAD OWN LITERAL WRITE.
 rewrite(imported_preflight_flag_agreement xs bytes REPR).
 destruct(preflight_certificate cell e le before k argv ofs p bytes STRCMP CHECK GLOBAL ARGV LOAD OWN LITERAL WRITE)
 as[after[STORE CERT]];exists after;split;[exact STORE|apply region_guaranteed;exact CERT].
Qed.
Theorem imported_export_flag_source cell e le before k argv ofs p xs bytes :
 validation_values xs=map Byte.unsigned bytes->
 e!_strcmp=None->e!___stringlit_132=None->e!_policy__1=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value p)->
 c_string before p bytes->c_string before(literal_address ___stringlit_132)files_bytes->
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 exists after,Mem.store Mint32 before main_policy_block 80(Val.of_bool(imported_export_flag xs))=Some after /\
 region_guarantee main_ge cell(flag_memory before after)(flag_frontier after(selection_after 17)k e le)11
 (State f_main(validation_suffix 17)k e le before).
Proof.
 intros REPR STRCMP FILES GLOBAL ARGV LOAD OWN LITERAL WRITE.
 rewrite(imported_export_flag_agreement xs bytes REPR).
 destruct(export_flag_certificate cell e le before k argv ofs p bytes STRCMP FILES GLOBAL ARGV LOAD OWN LITERAL WRITE)
 as[after[STORE CERT]];exists after;split;[exact STORE|apply region_guaranteed;exact CERT].
Qed.
