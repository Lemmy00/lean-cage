(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import ValidationStructure.
From LeanCageInitialization Require Import FlagStores ConfigurationMemory.
Open Scope Z_scope.
Theorem initialization_final_loads before flagged tree_set configured after flag tree stdin argv ofs :
 configuration_stores before flagged tree_set configured flag tree stdin->
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after->
 Mem.load Mint32 after main_policy_block 80=Some(Val.of_bool flag) /\
 Mem.load Mptr after(symbol_block _tree_digest)0=Some(address_value tree) /\
 Mem.load Mptr after(symbol_block _stdin_digest)0=Some(address_value stdin) /\
 Mem.load Mptr after main_policy_block 88=Some(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128))).
Proof.
 intros CONFIG STORE;destruct(configuration_loads _ _ _ _ _ _ _ CONFIG)as[FLAG[TREE STDIN]].
 destruct configuration_distinct as[PT[PS TS]];split.
 - rewrite(Mem.load_store_other _ _ _ _ _ _ STORE);[exact FLAG|right;left;change(80+4<=88);lia].
 - split.
   + rewrite(Mem.load_store_other _ _ _ _ _ _ STORE);[exact TREE|left;congruence].
   + split.
     * rewrite(Mem.load_store_other _ _ _ _ _ _ STORE);[exact STDIN|left;congruence].
     * rewrite(Mem.load_store_same _ _ _ _ _ _ STORE);reflexivity.
Qed.
