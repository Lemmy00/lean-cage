(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import ValidationStructure ValidationValues.
From LeanCageInitialization Require Import FlagStores StoreFrames.
Import ListNotations.
Open Scope Z_scope.
Definition configuration_stores before flagged tree_set configured flag tree stdin :=
 Mem.store Mint32 before main_policy_block 80(Val.of_bool flag)=Some flagged /\
 Mem.store Mptr flagged(symbol_block _tree_digest)0(address_value tree)=Some tree_set /\
 Mem.store Mptr tree_set(symbol_block _stdin_digest)0(address_value stdin)=Some configured.
Theorem configuration_frames before flagged tree_set configured flag tree stdin :
 configuration_stores before flagged tree_set configured flag tree stdin->
 setup_frame before flagged /\setup_frame before tree_set /\setup_frame before configured.
Proof.
 intros[FLAG[TREE STDIN]].
 assert(F:setup_frame before flagged)by(eapply setup_store_frame;[|exact FLAG];unfold setup_cell;auto 8).
 assert(T:setup_frame flagged tree_set)by(eapply setup_store_frame;[|exact TREE];unfold setup_cell;auto 8).
 assert(S:setup_frame tree_set configured)by(eapply setup_store_frame;[|exact STDIN];unfold setup_cell;auto 8).
 split;[exact F|];split;[eapply setup_frame_trans;eassumption|].
 eapply setup_frame_trans;[eapply setup_frame_trans;[exact F|exact T]|exact S].
Qed.
Theorem configuration_exists before flag tree stdin :
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 Mem.valid_access before Mptr(symbol_block _tree_digest)0 Writable->
 Mem.valid_access before Mptr(symbol_block _stdin_digest)0 Writable->
 exists flagged tree_set configured,configuration_stores before flagged tree_set configured flag tree stdin.
Proof.
 intros FW TW SW.
 destruct(Mem.valid_access_store before Mint32 main_policy_block 80(Val.of_bool flag)FW)as[flagged FLAG].
 assert(F:setup_frame before flagged)by(eapply setup_store_frame;[|exact FLAG];unfold setup_cell;auto 8).
 assert(TW':Mem.valid_access flagged Mptr(symbol_block _tree_digest)0 Writable)by(eapply setup_access;eassumption).
 destruct(Mem.valid_access_store flagged Mptr(symbol_block _tree_digest)0(address_value tree)TW')as[tree_set TREE].
 assert(T:setup_frame flagged tree_set)by(eapply setup_store_frame;[|exact TREE];unfold setup_cell;auto 8).
 assert(SW':Mem.valid_access tree_set Mptr(symbol_block _stdin_digest)0 Writable).
 { eapply setup_access;[eapply setup_frame_trans;[exact F|exact T]|exact SW]. }
 destruct(Mem.valid_access_store tree_set Mptr(symbol_block _stdin_digest)0(address_value stdin)SW')as[configured STDIN].
 exists flagged,tree_set,configured;split;[exact FLAG|];split;assumption.
Qed.
Definition configuration_prefix(before flagged tree_set configured current:mem) :=
 current=before \/current=flagged \/current=tree_set \/current=configured.
Theorem configuration_prefix_frame before flagged tree_set configured current flag tree stdin :
 configuration_stores before flagged tree_set configured flag tree stdin->
 configuration_prefix before flagged tree_set configured current->setup_frame before current.
Proof.
 intros STORES[EQ|[EQ|[EQ|EQ]]];subst current;[apply setup_frame_refl| | |];
 destruct(configuration_frames _ _ _ _ _ _ _ STORES)as[F[T S]];assumption.
Qed.
Lemma configuration_distinct : main_policy_block<>symbol_block _tree_digest /\
 main_policy_block<>symbol_block _stdin_digest /\symbol_block _tree_digest<>symbol_block _stdin_digest.
Proof. vm_compute;repeat split;discriminate. Qed.
Theorem configuration_loads before flagged tree_set configured flag tree stdin :
 configuration_stores before flagged tree_set configured flag tree stdin->
 Mem.load Mint32 configured main_policy_block 80=Some(Val.of_bool flag) /\
 Mem.load Mptr configured(symbol_block _tree_digest)0=Some(address_value tree) /\
 Mem.load Mptr configured(symbol_block _stdin_digest)0=Some(address_value stdin).
Proof.
 intros[FLAG[TREE STDIN]];destruct configuration_distinct as[PT[PS TS]].
 split.
 - rewrite(Mem.load_store_other _ _ _ _ _ _ STDIN)by auto.
   rewrite(Mem.load_store_other _ _ _ _ _ _ TREE)by auto.
   apply flag_store_load with(before:=before);exact FLAG.
 - split.
   + rewrite(Mem.load_store_other _ _ _ _ _ _ STDIN)by auto.
     rewrite(Mem.load_store_same _ _ _ _ _ _ TREE);reflexivity.
   + rewrite(Mem.load_store_same _ _ _ _ _ _ STDIN);reflexivity.
Qed.
