(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Construct inhabited full-program memories and source executions. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Readers WriteMemory Library FreshMemoryDraft Machine.
From LeanCageMain Require Import Main MainStructure MainGlobals.
From LeanCageArguments Require Import StringMachine StringPath ArgumentAllocation.
From LeanCageDigest Require Import DigestStructure DigestWords DigestSource.
Import ListNotations.
Open Scope Z_scope.
Definition digest_input_admissible bytes := Forall(fun b=>b<>Byte.zero)bytes /\
 Z.of_nat(length bytes)+1<=Int64.max_unsigned.
Definition digest_input_admissibleb bytes := forallb(fun b=>negb(Byte.eq b Byte.zero))bytes&&
 (Z.of_nat(length bytes)+1<=?Int64.max_unsigned).
Lemma digest_input_admissible_sound bytes : digest_input_admissibleb bytes=true->digest_input_admissible bytes.
Proof.
 intros VALID;apply andb_true_iff in VALID;destruct VALID as[NONZERO SIZE];split;[|apply Z.leb_le;exact SIZE].
 apply Forall_forall;intros b IN;rewrite forallb_forall in NONZERO;specialize(NONZERO b IN).
 apply negb_true_iff in NONZERO;intro EQ;subst;rewrite Byte.eq_true in NONZERO;discriminate.
Qed.
Theorem allocated_digest_source cell bytes : digest_input_admissible bytes->
 exists initial m p count,Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\
 c_string m p bytes /\ (count<=2068)%nat /\
 string_path main_ge cell(digest_initial(address_value p)Kstop m)count
 (Returnstate(Val.of_bool(digest_valid bytes))Kstop m).
Proof.
 intros[NONZERO SIZE];destruct native_initial_memory_exists as[initial INIT].
 destruct(allocate_guest_string initial bytes NONZERO SIZE)as[m[p[OLD OWN]]].
 destruct(digest_source cell m p bytes Kstop OWN)as[count[BOUND PATH]].
 exists initial,m,p,count;auto.
Qed.
Theorem allocate_digest_prefix base bytes suffix : digest_input_admissible bytes->
 exists after p,old_memory base after /\
 Mem.loadbytes after(address_block p)(address_offset p)(Z.of_nat(length(bytes++Byte.zero::suffix)))=
 Some(map Byte(bytes++Byte.zero::suffix)) /\ c_string after p bytes.
Proof.
 intros[NONZERO BOUND];destruct(allocated_bytes base(bytes++Byte.zero::suffix))
 as[allocated[b[after[ALLOC[STORE LOAD]]]]].
 assert(FRESH:~Mem.valid_block base b)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 exists after,({|address_block:=b;address_offset:=0|});split.
 - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
   eapply Mem.storebytes_unchanged_on;[exact STORE|];intros pos RANGE VALID;contradiction.
 - split;[exact LOAD|];split;[exact NONZERO|];split.
   + unfold span_bounds;cbn[address_offset];rewrite length_app.
     change(0<=0<Ptrofs.modulus /\ 0+Z.of_nat(length bytes+1)<=Ptrofs.modulus /\
      Z.of_nat(length bytes+1)<=Int64.max_unsigned).
     rewrite Nat2Z.inj_add;change Ptrofs.modulus with 18446744073709551616;
     change Int64.max_unsigned with 18446744073709551615 in *;lia.
   + replace(bytes++Byte.zero::suffix)with((bytes++[Byte.zero])++suffix)in LOAD by(rewrite<-app_assoc;reflexivity).
     exact(load_first _ _ _ _ _ LOAD).
Qed.
Theorem digest_trailing_bytes_source cell bytes suffix : digest_input_admissible bytes->
 exists initial m p count,Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\
 Mem.loadbytes m(address_block p)(address_offset p)(Z.of_nat(length(bytes++Byte.zero::suffix)))=
 Some(map Byte(bytes++Byte.zero::suffix)) /\ (count<=2068)%nat /\
 string_path main_ge cell(digest_initial(address_value p)Kstop m)count
 (Returnstate(Val.of_bool(digest_valid bytes))Kstop m).
Proof.
 intros VALID;destruct native_initial_memory_exists as[initial INIT].
 destruct(allocate_digest_prefix initial bytes suffix VALID)as[m[p[OLD[RAW OWN]]]].
 destruct(digest_source cell m p bytes Kstop OWN)as[count[BOUND PATH]].
 exists initial,m,p,count;auto.
Qed.
