(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Library.
From LeanCageMain Require Import Main MainStructure MainFields.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import ArgumentMemory.
From LeanCageValidation Require Import ValidationStructure ValidationMemory ValidationAllocation.
From LeanCageInitialization Require Import FlagStores.
Import ListNotations.
Open Scope Z_scope.
Definition setup_outside b pos :=
 store_outside(symbol_block _preflight)0 4 b pos /\store_outside main_policy_block 80 4 b pos /\
 store_outside(symbol_block _tree_digest)0 8 b pos /\store_outside(symbol_block _stdin_digest)0 8 b pos /\
 store_outside main_policy_block 88 8 b pos.
Definition same_permissions(before after:mem) := forall b pos kind perm,
 Mem.perm after b pos kind perm<->Mem.perm before b pos kind perm.
Definition setup_frame before after := Mem.unchanged_on setup_outside before after /\same_permissions before after.
Lemma setup_frame_refl m : setup_frame m m.
Proof. split;[apply Mem.unchanged_on_refl|unfold same_permissions;intros;tauto]. Qed.
Lemma setup_frame_trans a b c : setup_frame a b->setup_frame b c->setup_frame a c.
Proof. intros[AB AP][BC BP];unfold same_permissions in *;split;[eapply Mem.unchanged_on_trans;eassumption|intros x pos kind perm;rewrite BP,AP;tauto]. Qed.
Definition setup_cell chunk b ofs :=
 (chunk=Mint32 /\b=symbol_block _preflight /\ofs=0) \/
 (chunk=Mint32 /\b=main_policy_block /\ofs=80) \/
 (chunk=Mptr /\b=symbol_block _tree_digest /\ofs=0) \/
 (chunk=Mptr /\b=symbol_block _stdin_digest /\ofs=0) \/
 (chunk=Mptr /\b=main_policy_block /\ofs=88).
Lemma setup_cell_outside chunk b ofs : setup_cell chunk b ofs->forall block pos,
 setup_outside block pos->store_outside b ofs(size_chunk chunk)block pos.
Proof.
 intros[[-> [-> ->]]|[[-> [-> ->]]|[[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]]]]block pos[A[B[C[D E]]]];
 first[exact A|exact B|exact C|exact D|exact E].
Qed.
Theorem setup_store_frame before after chunk b ofs value : setup_cell chunk b ofs->
 Mem.store chunk before b ofs value=Some after->setup_frame before after.
Proof.
 intros CELL STORE;split.
 - eapply Mem.unchanged_on_implies;[eapply single_store_outside;exact STORE|].
   intros block pos OUT VALID;eapply setup_cell_outside;[exact CELL|exact OUT].
 - unfold same_permissions;intros block pos kind perm;split;intros ACCESS;
   [eapply Mem.perm_store_2|eapply Mem.perm_store_1];eassumption.
Qed.
Definition setup_separate b := b<>symbol_block _preflight /\b<>main_policy_block /\
 b<>symbol_block _tree_digest /\b<>symbol_block _stdin_digest.
Lemma separate_outside b : setup_separate b->forall pos,setup_outside b pos.
Proof. intros[A[B[C D]]]pos;repeat split;left;assumption. Qed.
Theorem setup_string before after p bytes : setup_frame before after->setup_separate(address_block p)->
 c_string before p bytes->c_string after p bytes.
Proof.
 intros[OLD PERM]SEP[NOZERO[SPAN LOAD]];split;[exact NOZERO|];split;[exact SPAN|].
 eapply Mem.loadbytes_unchanged_on;[exact OLD|intros;apply separate_outside;exact SEP|exact LOAD].
Qed.
Theorem setup_load before after b chunk ofs value : setup_frame before after->setup_separate b->
 Mem.loadv chunk before(Vptr b ofs)=Some value->Mem.loadv chunk after(Vptr b ofs)=Some value.
Proof.
 intros[OLD PERM]SEP LOAD;unfold Mem.loadv in *;destruct(zle _ _);[|discriminate].
 eapply Mem.load_unchanged_on;[exact OLD|intros;apply separate_outside;exact SEP|exact LOAD].
Qed.
Theorem setup_access before after b chunk ofs perm : setup_frame before after->
 Mem.valid_access before chunk b ofs perm->Mem.valid_access after chunk b ofs perm.
Proof.
 intros[OLD PERM][RANGE ALIGN];split;[|exact ALIGN].
 intros pos WITHIN;apply PERM;apply RANGE;exact WITHIN.
Qed.
Theorem setup_literal_blocks : Forall(fun item=>setup_separate(address_block(literal_address(fst item))))literal_cases.
Proof. repeat(apply Forall_cons;[vm_compute;repeat split;discriminate|]);constructor. Qed.
Theorem setup_literals before after : setup_frame before after->literals_owned before->literals_owned after.
Proof.
 intros FRAME OWN;unfold literals_owned;apply Forall_forall;intros item IN.
 pose proof setup_literal_blocks as SEP;rewrite Forall_forall in SEP.
 unfold literals_owned in OWN;rewrite Forall_forall in OWN.
 eapply setup_string;[exact FRAME|apply SEP;exact IN|apply OWN;exact IN].
Qed.
Theorem setup_guest_arguments before after argv ofs i inputs : setup_frame before after->setup_separate argv->
 Forall(fun x=>setup_separate(address_block(guest_pointer x)))inputs->
 guest_arguments_owned before argv ofs i inputs->guest_arguments_owned after argv ofs i inputs.
Proof.
 intros FRAME ARGV SEP;revert i;induction SEP as[|x xs HEAD REST IH];intros i OWN;cbn in *;[exact I|].
 destruct OWN as[TEXT[LOAD TAIL]];split;[eapply setup_string;eassumption|];split;
 [eapply setup_load;eassumption|apply IH;exact TAIL].
Qed.
Lemma policy_other_globals : main_policy_block<>symbol_block _preflight /\
 main_policy_block<>symbol_block _tree_digest /\main_policy_block<>symbol_block _stdin_digest.
Proof. vm_compute;repeat split;discriminate. Qed.
Theorem setup_policy_image before after values : setup_frame before after->policy_image before values->policy_image after values.
Proof.
 intros[OLD PERM][LEN[RANGE READ]];split;[exact LEN|];split;[exact RANGE|].
 intros i id IN;pose proof(policy_field_index i id IN)as INDEX;specialize(READ i id IN).
 unfold Mem.loadv in *;destruct(zle _ _);[|discriminate].
 eapply Mem.load_unchanged_on;[exact OLD| |exact READ].
 intros pos SPAN;rewrite Ptrofs.unsigned_repr in SPAN by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
 change(8*i<=pos<8*i+8)in SPAN;destruct policy_other_globals as[PF[TREE STDIN]].
 unfold setup_outside,store_outside;repeat split;auto;lia.
Qed.
