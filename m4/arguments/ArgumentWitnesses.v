(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Construct actual global-memory and argument-table witnesses. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Machine Library FreshMemoryDraft WriteAll.
From LeanCageMain Require Import Main MainStructure MainGlobals MainMemory.
From LeanCageBounds Require Import BoundsMemory BoundsWitnesses.
From LeanCageArguments Require Import StringMachine StringPath ArgumentStructure ArgumentMemory
 ArgumentAllocation ArgumentSource ArgumentBounds.
Import ListNotations.
Open Scope Z_scope.
Definition argument_witness_env argv argc := PTree.set _argv(Vptr argv Ptrofs.zero)
 (PTree.set _argc(Vint(Int.repr argc))(create_undef_temps(fn_temps f_main))).
Lemma old_policy_image before after values : old_memory before after ->
 policy_image before values -> policy_image after values.
Proof.
 intros OLD[LEN[RANGE READ]];split;[exact LEN|];split;[exact RANGE|];intros i id IN.
 eapply old_memory_loadv;[exact OLD|apply READ with(id:=id);exact IN].
Qed.
Definition admissible_guest_sources sources :=
 (1<=length sources)%nat /\ Z.of_nat(length sources)<=2147483647-16 /\
 Forall(fun bytes=>Forall(fun b=>b<>Byte.zero)bytes /\ Z.of_nat(length bytes)+1<=Int64.max_unsigned)sources.
Theorem allocated_argument_source cell sources : admissible_guest_sources sources ->
 exists initial m argv inputs count final,
 Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\ map guest_bytes inputs=sources /\
 (count<=26*length sources+13)%nat /\
 string_path main_ge cell
 (State f_main argument_suffix Kstop(PTree.empty _)(argument_witness_env argv(16+Z.of_nat(length sources)))m)
 count(argument_endpoint(argument_scan_bytes 16 0 sources)(PTree.empty _)final Kstop m).
Proof.
 intros[NONEMPTY[COUNT STRINGS]].
 destruct native_initial_memory_exists as[initial INIT].
 destruct(allocated_guest_inputs initial sources STRINGS COUNT)as[m[argv[inputs[OLD[BYTES[SPAN OWN]]]]]].
 assert(LEN:length inputs=length sources)by(rewrite<-BYTES,length_map;reflexivity).
 destruct(argument_region_source cell m argv Ptrofs.zero
 (16+Z.of_nat(length sources))inputs(PTree.empty _)(argument_witness_env argv(16+Z.of_nat(length sources)))Kstop
 ltac:(lia)ltac:(lia)ltac:(rewrite LEN in SPAN;exact SPAN)OWN eq_refl
 ltac:(unfold argument_witness_env;WriteAll.lookup)ltac:(unfold argument_witness_env;WriteAll.lookup))
 as[n[final[BOUND[REG PATH]]]].
 exists initial,m,argv,inputs,n,final;split;[exact INIT|];split;[exact OLD|];split;[exact BYTES|];split;[lia|].
 rewrite argument_scan_representation,BYTES in PATH;exact PATH.
Qed.
Theorem allocated_argument_bounds cell sources values : admissible_guest_sources sources ->
 length values=10%nat -> Forall(fun v=>0<=v<=Int64.max_unsigned)values ->
 exists initial configured m argv inputs count final,
 Genv.init_mem Main.prog=Some initial /\ policy_stores main_policy_block 0 initial values configured /\
 old_memory configured m /\ map guest_bytes inputs=sources /\
 (count<=26*length sources+154)%nat /\
 string_path main_ge cell
 (State f_main argument_suffix Kstop(PTree.empty _)(argument_witness_env argv(16+Z.of_nat(length sources)))m)
 count(argument_bounds_endpoint(16+Z.of_nat(length sources))inputs values(PTree.empty _)final Kstop m).
Proof.
 intros[NONEMPTY[COUNT STRINGS]]LEN WIDTH.
 destruct(allocated_policy_image values LEN WIDTH)as[initial[configured[INIT[STORES IMAGE]]]].
 destruct(allocated_guest_inputs configured sources STRINGS COUNT)as[m[argv[inputs[OLD[BYTES[SPAN OWN]]]]]].
 assert(SIZE:length inputs=length sources)by(rewrite<-BYTES,length_map;reflexivity).
 destruct(argument_bounds_source cell m argv Ptrofs.zero(16+Z.of_nat(length sources))inputs values
 (PTree.empty _)(argument_witness_env argv(16+Z.of_nat(length sources)))Kstop
 ltac:(lia)ltac:(lia)ltac:(rewrite SIZE in SPAN;exact SPAN)OWN eq_refl eq_refl
 (old_policy_image _ _ _ OLD IMAGE)
 ltac:(unfold argument_witness_env;WriteAll.lookup)ltac:(unfold argument_witness_env;WriteAll.lookup))
 as[n[final[BOUND PATH]]].
 exists initial,configured,m,argv,inputs,n,final;split;[exact INIT|];split;[exact STORES|];split;[exact OLD|];
 split;[exact BYTES|];split;[lia|exact PATH].
Qed.
Theorem allocated_aliased_arguments cell bytes : Forall(fun b=>b<>Byte.zero)bytes ->
 Z.of_nat(length bytes)+1<=Int64.max_unsigned ->
 exists initial m argv p count final,
 Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\
 guest_arguments_owned m argv Ptrofs.zero 16
 [{|guest_pointer:=p;guest_bytes:=bytes|};{|guest_pointer:=p;guest_bytes:=bytes|}] /\
 (count<=65)%nat /\ string_path main_ge cell
 (State f_main argument_suffix Kstop(PTree.empty _)(argument_witness_env argv 18)m)count
 (argument_endpoint(argument_scan_bytes 16 0[bytes;bytes])(PTree.empty _)final Kstop m).
Proof.
 intros NONZERO LENGTH;destruct native_initial_memory_exists as[initial INIT].
 destruct(allocate_guest_string initial bytes NONZERO LENGTH)as[mid[p[OLD STRING]]].
 set(x:={|guest_pointer:=p;guest_bytes:=bytes|}).
 assert(STRINGS:guest_strings_owned mid[x;x])by(constructor;[exact STRING|constructor;[exact STRING|constructor]]).
 destruct(allocate_guest_table mid[x;x]STRINGS ltac:(cbn;lia))as[m[argv[MORE[SPAN OWN]]]].
 destruct(argument_region_source cell m argv Ptrofs.zero 18[x;x](PTree.empty _)(argument_witness_env argv 18)Kstop
 ltac:(lia)eq_refl SPAN OWN eq_refl ltac:(unfold argument_witness_env;WriteAll.lookup)
 ltac:(unfold argument_witness_env;WriteAll.lookup))as[n[final[BOUND[REG PATH]]]].
 exists initial,m,argv,p,n,final;split;[exact INIT|];split.
 - eapply Mem.unchanged_on_trans;[exact OLD|].
   eapply Mem.unchanged_on_implies;[exact MORE|];intros b pos VALIDBASE VALIDMID;exact VALIDMID.
 - split;[exact OWN|];split;[exact BOUND|].
   rewrite argument_scan_representation in PATH;exact PATH.
Qed.
