(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Allocate owned strings without changing existing memory. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Readers Library FreshMemoryDraft ScalarMemory.
From LeanCageArguments Require Import ArgumentMemory.
Import ListNotations.
Open Scope Z_scope.
Definition guest_strings_owned m inputs := Forall(fun x=>c_string m(guest_pointer x)(guest_bytes x))inputs.
Lemma old_memory_loadv before after chunk pointer value : old_memory before after ->
 Mem.loadv chunk before pointer=Some value -> Mem.loadv chunk after pointer=Some value.
Proof.
 intros OLD LOAD;destruct pointer;cbn in LOAD;try discriminate.
 unfold Mem.loadv;destruct(zle _ _)eqn:SPAN;[eapply old_memory_load;eassumption|discriminate].
Qed.
Lemma old_guest_strings before after inputs : old_memory before after ->
 guest_strings_owned before inputs -> guest_strings_owned after inputs.
Proof.
 intros OLD OWN;induction OWN;constructor;auto;eapply old_memory_string;eassumption.
Qed.
Theorem allocate_guest_string base bytes : Forall(fun b=>b<>Byte.zero)bytes ->
 Z.of_nat(length bytes)+1<=Int64.max_unsigned ->
 exists after p,old_memory base after /\ c_string after p bytes.
Proof.
 intros NONZERO BOUND;destruct(allocated_bytes base(bytes++[Byte.zero]))
 as[allocated[b[after[ALLOC[STORE LOAD]]]]].
 assert(FRESH:~Mem.valid_block base b)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 exists after,({|address_block:=b;address_offset:=0|});split.
 - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
   eapply Mem.storebytes_unchanged_on;[exact STORE|];intros pos RANGE VALID;contradiction.
 - split;[exact NONZERO|];split.
   + unfold span_bounds;cbn[address_offset];rewrite length_app;change
     (0<=0<Ptrofs.modulus /\ 0+Z.of_nat(length bytes+1)<=Ptrofs.modulus /\
      Z.of_nat(length bytes+1)<=Int64.max_unsigned).
     rewrite Nat2Z.inj_add;change Ptrofs.modulus with 18446744073709551616;
     change Int64.max_unsigned with 18446744073709551615 in *;lia.
   + exact LOAD.
Qed.
Theorem allocate_guest_strings base sources :
 Forall(fun bytes=>Forall(fun b=>b<>Byte.zero)bytes /\ Z.of_nat(length bytes)+1<=Int64.max_unsigned)sources ->
 exists after inputs,old_memory base after /\ map guest_bytes inputs=sources /\ guest_strings_owned after inputs.
Proof.
 intros VALID;revert base;induction VALID as[|bytes rest[NONZERO LENGTH]REST IH];intros base.
 - exists base,[];split;[apply Mem.unchanged_on_refl|];split;[reflexivity|constructor].
 - destruct(allocate_guest_string base bytes NONZERO LENGTH)as[mid[p[OLD STRING]]].
   destruct(IH mid)as[after[inputs[MORE[BYTES OWN]]]].
   exists after,({|guest_pointer:=p;guest_bytes:=bytes|}::inputs);split.
   + eapply Mem.unchanged_on_trans;[exact OLD|].
     eapply Mem.unchanged_on_implies;[exact MORE|];intros b pos VALIDBASE VALIDMID;exact VALIDMID.
   + split;[cbn;congruence|];constructor;[eapply old_memory_string;eassumption|exact OWN].
Qed.
Fixpoint guest_cells i inputs := match inputs with
|[]=>[]|x::rest=>{|scalar_chunk:=Mptr;scalar_offset:=8*i;
 scalar_value:=address_value(guest_pointer x)|}::guest_cells(i+1)rest end.
Lemma guest_cells_valid i inputs argc : 0<=i -> i+Z.of_nat(length inputs)<=argc ->
 Forall(scalar_valid(8*argc))(guest_cells i inputs).
Proof.
 revert i;induction inputs as[|x rest IH];intros i LOW HIGH;[constructor|];constructor.
 - change(0<=8*i /\ 8*i+8<=8*argc /\(8|8*i));split;[lia|];split;[cbn in HIGH;lia|exists i;ring].
 - apply IH;[lia|cbn in HIGH;lia].
Qed.
Lemma guest_cells_lower i inputs : Forall(fun c=>8*i<=scalar_offset c)(guest_cells i inputs).
Proof.
 revert i;induction inputs as[|x rest IH];intros i;[constructor|];constructor;[change(8*i<=8*i);lia|].
 eapply Forall_impl with(P:=fun c=>8*(i+1)<=scalar_offset c);[intros c BOUND;lia|apply IH].
Qed.
Lemma guest_cells_ordered i inputs : scalar_orderedb(guest_cells i inputs)=true.
Proof.
 revert i;induction inputs as[|x rest IH];intros i;[reflexivity|].
 cbn[guest_cells scalar_orderedb];apply Bool.andb_true_iff;split;[|apply IH].
 apply forallb_forall;intros c IN;apply Z.leb_le.
 pose proof(guest_cells_lower(i+1)rest)as LOWER;rewrite Forall_forall in LOWER;specialize(LOWER c IN).
 change(8*i+8<=scalar_offset c);lia.
Qed.
Lemma guest_table_from_cells m argv i inputs argc :
 0<=i -> i+Z.of_nat(length inputs)<=argc -> 8*argc<=Ptrofs.modulus ->
 guest_strings_owned m inputs ->
 Forall(fun c=>Mem.load(scalar_chunk c)m argv(scalar_offset c)=
  Some(Val.load_result(scalar_chunk c)(scalar_value c)))(guest_cells i inputs) ->
 guest_arguments_owned m argv Ptrofs.zero i inputs.
Proof.
 revert i;induction inputs as[|x rest IH];intros i LOW COUNT HIGH OWN LOADS;[exact I|].
 inversion OWN as[|? ? STRING STRINGS];subst;inversion LOADS as[|? ? LOAD MORE];subst.
 split;[exact STRING|];split.
 - rewrite Ptrofs.add_zero_l;unfold Mem.loadv.
   rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;cbn in COUNT;lia).
   destruct(zle _ _)as[SPAN|OVER];[exact LOAD|].
   change(8*i+8>Ptrofs.modulus)in OVER;cbn in COUNT;lia.
 - apply IH;try assumption;cbn in COUNT;lia.
Qed.
Theorem allocate_guest_table base inputs : guest_strings_owned base inputs ->
 Z.of_nat(length inputs)<=2147483647-16 ->
 exists after argv,old_memory base after /\
 guest_table_span Ptrofs.zero(16+Z.of_nat(length inputs)) /\
 guest_arguments_owned after argv Ptrofs.zero 16 inputs.
Proof.
 intros OWN COUNT;set(argc:=16+Z.of_nat(length inputs));set(size:=8*argc).
 destruct(Mem.alloc base 0 size)as[allocated argv]eqn:ALLOC.
 assert(FRESH:~Mem.valid_block base argv)by(eapply Mem.fresh_block_alloc;exact ALLOC).
 assert(VALID:Forall(scalar_valid size)(guest_cells 16 inputs)).
 { apply guest_cells_valid;[lia|unfold argc;lia]. }
 destruct(scalar_stores_exist argv size(guest_cells 16 inputs)allocated VALID)
 as[after STORES].
 { red;intros pos RANGE;eapply Mem.perm_alloc_2;[exact ALLOC|exact RANGE]. }
 assert(OLD:old_memory base after).
 { eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
   eapply Mem.unchanged_on_implies;[eapply scalar_stores_outside;[exact STORES|exact VALID]|].
   intros b pos VALIDBASE VALIDALLOC;left;intro EQ;subst;contradiction. }
 exists after,argv;split;[exact OLD|];split.
 - unfold guest_table_span;change(Ptrofs.unsigned Ptrofs.zero)with 0.
   change Ptrofs.modulus with 18446744073709551616;lia.
 - apply guest_table_from_cells with(argc:=argc);
   [lia|unfold argc;lia|unfold argc;change Ptrofs.modulus with 18446744073709551616;lia| |].
   + eapply old_guest_strings;eassumption.
   + apply Forall_forall;intros c IN;eapply scalar_stores_fields;
     [exact STORES|apply scalar_orderedb_sound;apply guest_cells_ordered|exact IN].
Qed.
Theorem allocated_guest_inputs base sources :
 Forall(fun bytes=>Forall(fun b=>b<>Byte.zero)bytes /\ Z.of_nat(length bytes)+1<=Int64.max_unsigned)sources ->
 Z.of_nat(length sources)<=2147483647-16 ->
 exists after argv inputs,old_memory base after /\ map guest_bytes inputs=sources /\
 guest_table_span Ptrofs.zero(16+Z.of_nat(length inputs)) /\
 guest_arguments_owned after argv Ptrofs.zero 16 inputs.
Proof.
 intros STRINGS COUNT;destruct(allocate_guest_strings base sources STRINGS)
 as[mid[inputs[OLD[BYTES OWN]]]].
 assert(LEN:length inputs=length sources)by(rewrite<-BYTES,length_map;reflexivity).
 destruct(allocate_guest_table mid inputs OWN ltac:(lia))as[after[argv[MORE[SPAN ARGS]]]].
 exists after,argv,inputs;split.
 - eapply Mem.unchanged_on_trans;[exact OLD|].
   eapply Mem.unchanged_on_implies;[exact MORE|];intros b pos VALIDBASE VALIDMID;exact VALIDMID.
 - split;[exact BYTES|];split;[exact SPAN|exact ARGS].
Qed.
