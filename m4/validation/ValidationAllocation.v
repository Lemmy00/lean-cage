(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
Require Import Readers WriteMemory Library FreshMemoryDraft ScalarMemory.
From LeanCageMain Require Import Main MainStructure MainGlobals.
From LeanCageArguments Require Import ArgumentAllocation.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationMemory.
Import ListNotations.
Open Scope Z_scope.
Definition literal_cases := [( ___stringlit_56,none_bytes);(___stringlit_133,discard_bytes);
 (___stringlit_132,files_bytes);(___stringlit_135,shell_bytes);(___stringlit_134,python_bytes);
 (___stringlit_131,plan_bytes);(___stringlit_130,check_bytes)].
Definition literals_owned m := Forall(fun input=>c_string m(literal_address(fst input))(snd input))literal_cases.
Lemma literals_initial m : Genv.init_mem Main.prog=Some m->literals_owned m.
Proof.
 intros INIT;repeat(apply Forall_cons;[first[apply initial_none|apply initial_discard|apply initial_files|
 apply initial_shell|apply initial_python|apply initial_plan|apply initial_check];exact INIT|]);constructor.
Qed.
Lemma literal_owned m id bytes : literals_owned m->In(id,bytes)literal_cases->c_string m(literal_address id)bytes.
Proof. intros OWN IN;unfold literals_owned in OWN;rewrite Forall_forall in OWN;exact(OWN(id,bytes)IN). Qed.
Ltac owned_literal := eapply literal_owned;[eassumption|unfold literal_cases;cbn;auto 12].
Lemma literals_old before after : old_memory before after->literals_owned before->literals_owned after.
Proof.
 intros OLD OWN;eapply Forall_impl;[|exact OWN];intros input TEXT;eapply old_memory_string;eassumption.
Qed.
Lemma old_valid_access before after chunk b ofs perm : old_memory before after->
 Mem.valid_access before chunk b ofs perm->Mem.valid_access after chunk b ofs perm.
Proof.
 intros OLD[ACCESS ALIGN];split;[|exact ALIGN];red;intros pos RANGE.
 eapply Mem.perm_unchanged_on;[exact OLD| |apply ACCESS;exact RANGE].
 eapply Mem.perm_valid_block;apply ACCESS;exact RANGE.
Qed.
Lemma validation_pointer_initial m id : Genv.init_mem Main.prog=Some m->
 In id[_tree_digest;_stdin_digest]->Mem.valid_access m Mptr(symbol_block id)0 Writable.
Proof.
 intros INIT[<-|[<-|BAD]];[| |contradiction].
 - assert(VAR:Genv.find_var_info(Genv.globalenv Main.prog)(symbol_block _tree_digest)=Some v_tree_digest)by reflexivity.
   pose proof(proj1(Genv.init_mem_characterization Main.prog(symbol_block _tree_digest)VAR INIT))as RANGE.
   split;[exact RANGE|exists 0;reflexivity].
 - assert(VAR:Genv.find_var_info(Genv.globalenv Main.prog)(symbol_block _stdin_digest)=Some v_stdin_digest)by reflexivity.
   pose proof(proj1(Genv.init_mem_characterization Main.prog(symbol_block _stdin_digest)VAR INIT))as RANGE.
   split;[exact RANGE|exists 0;reflexivity].
Qed.
Lemma validation_policy_args_initial m : Genv.init_mem Main.prog=Some m->
 Mem.valid_access m Mptr main_policy_block 88 Writable.
Proof.
 intros INIT;destruct(native_policy_permissions _ INIT)as[RANGE _];split;[|exists 11;reflexivity].
 red;intros pos BOUND;apply RANGE;change(88<=pos<88+8)in BOUND;lia.
Qed.
Theorem allocate_fresh_string base bytes : digest_input_admissible bytes->
 exists after p,old_memory base after /\ c_string after p bytes /\ ~Mem.valid_block base(address_block p).
Proof.
 intros[NONZERO BOUND];destruct(allocated_bytes base(bytes++[Byte.zero]))
 as[allocated[b[after[ALLOC[STORE LOAD]]]]].
 assert(FRESH:~Mem.valid_block base b)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 exists after,({|address_block:=b;address_offset:=0|});split.
 - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
   eapply Mem.storebytes_unchanged_on;[exact STORE|];intros pos RANGE VALID;contradiction.
 - split;[|exact FRESH];split;[exact NONZERO|];split.
   + unfold span_bounds;cbn[address_offset];rewrite length_app;change
     (0<=0<Ptrofs.modulus /\ 0+Z.of_nat(length bytes+1)<=Ptrofs.modulus /\
      Z.of_nat(length bytes+1)<=Int64.max_unsigned).
     rewrite Nat2Z.inj_add;change Ptrofs.modulus with 18446744073709551616;
     change Int64.max_unsigned with 18446744073709551615 in *;lia.
   + exact LOAD.
Qed.
Theorem allocate_selected_pointer base index p : 0<=index<=16->
 exists after argv,old_memory base after /\
 Mem.loadv Mptr after(Vptr argv(Ptrofs.repr(8*index)))=Some(address_value p) /\
 ~Mem.valid_block base argv.
Proof.
 intros INDEX;destruct(Mem.alloc base 0 136)as[allocated argv]eqn:ALLOC.
 assert(FRESH:~Mem.valid_block base argv)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 assert(ACCESS:Mem.valid_access allocated Mptr argv(8*index)Writable).
 { eapply Mem.valid_access_implies with(p1:=Freeable);[|constructor].
   eapply Mem.valid_access_alloc_same;[exact ALLOC|change(0<=8*index);lia|change(8*index+8<=136);lia|change(8|8*index);exists index;ring]. }
 destruct(Mem.valid_access_store _ _ _ _ (address_value p)ACCESS)as[after STORE].
 exists after,argv;split.
 - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
   eapply Mem.store_unchanged_on;[exact STORE|];intros pos RANGE VALID;contradiction.
 - split;[|exact FRESH];unfold Mem.loadv;rewrite Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
   destruct(zle _ _)as[SPAN|BAD];[exact(Mem.load_store_same _ _ _ _ _ _ STORE)|].
   change(8*index+8>18446744073709551616)in BAD;lia.
Qed.
Lemma string_store_other m after p bytes block ofs value :
 Mem.store Mptr m block ofs value=Some after->address_block p<>block->c_string m p bytes->c_string after p bytes.
Proof.
 intros STORE NE[NZ[SPAN LOAD]];split;[exact NZ|];split;[exact SPAN|].
 erewrite Mem.loadbytes_store_other;eauto.
Qed.
Lemma literals_store_other m after b ofs value : Mem.store Mptr m b ofs value=Some after->
 (forall id,In id validation_literals->symbol_block id<>b)->literals_owned m->literals_owned after.
Proof.
 intros STORE SEPARATE OWN;apply Forall_forall;intros[id bytes]IN.
 eapply string_store_other;[exact STORE| |eapply literal_owned;eassumption].
 apply SEPARATE;unfold literal_cases in IN;cbn in IN;
 repeat destruct IN as[EQ|IN];try contradiction;inversion EQ;subst;
 unfold validation_literals;cbn;auto 12.
Qed.
Lemma literals_separate_globals id : In id[_tree_digest;_stdin_digest;_policy__1]->
 forall literal,In literal validation_literals->symbol_block literal<>symbol_block id.
Proof.
 intros[<-|[<-|[<-|BAD]]]literal IN;try contradiction;
 unfold validation_literals in IN;repeat destruct IN as[<-|IN];try contradiction;vm_compute;discriminate.
Qed.
Lemma global_pointer_distinct : symbol_block _tree_digest<>symbol_block _stdin_digest.
Proof. vm_compute;discriminate. Qed.
Lemma pointer_load_store_other m after store_block store_ofs store_value block ofs value :
 Mem.store Mptr m store_block store_ofs store_value=Some after->block<>store_block->
 Mem.loadv Mptr m(Vptr block ofs)=Some value->Mem.loadv Mptr after(Vptr block ofs)=Some value.
Proof.
 intros STORE NE LOAD;unfold Mem.loadv in *;destruct(zle _ _);[|exact LOAD].
 erewrite Mem.load_store_other;eauto.
Qed.
