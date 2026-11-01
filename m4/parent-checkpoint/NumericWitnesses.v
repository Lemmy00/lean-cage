(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine Library FreshMemoryDraft ScalarMemory WriteAll.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainFields MainEntry MainSource.
From LeanCageArguments Require Import ArgumentMemory ArgumentWitnesses.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues ValidationAllocation.
From LeanCageInitialization Require Import StoreFrames InitializationAllocation.
From LeanCageParent Require Import ParentMemory ParentAllocation NumericMemory NumericComposition
 ValidationLocals ValidationAllocation ValidationInputs.
Import ListNotations.
Open Scope Z_scope.
Theorem allocated_numeric_validation cell textfields bytes export_bytes tree_bytes stdin_bytes sources :
 length textfields=10%nat->Forall digest_input_admissible textfields->
 digest_input_admissible bytes->digest_input_admissible export_bytes->digest_input_admissible tree_bytes->digest_input_admissible stdin_bytes->
 admissible_guest_sources sources->
 exists initial before fields output argv inputs export tree stdin x rest initialized numeric_count numeric final,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 map input_bytes inputs=textfields /\map guest_bytes(x::rest)=sources /\
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(numeric_values inputs)numeric /\
 validation_frame(argument_witness_env argv(16+Z.of_nat(length sources)))final /\
 numeric_validation_contract cell(validation_locals fields output)(argument_witness_env argv(16+Z.of_nat(length sources)))before Kstop
 fields inputs initialized numeric_count numeric final(16+Z.of_nat(length sources))argv Ptrofs.zero bytes output
 export tree stdin export_bytes tree_bytes stdin_bytes x rest.
Proof.
 intros LEN NUMVALID PVALID EVALID TVALID SVALID[NONEMPTY[COUNT GUESTVALID]].
 assert(VALID:Forall digest_input_admissible(textfields++bytes::export_bytes::tree_bytes::stdin_bytes::sources)).
 { apply Forall_app;split;[exact NUMVALID|];constructor;[exact PVALID|];constructor;[exact EVALID|];constructor;[exact TVALID|];constructor;assumption. }
 assert(SOURCECOUNT:Z.of_nat(length(textfields++bytes::export_bytes::tree_bytes::stdin_bytes::sources))<=2147483647-2).
 { rewrite length_app,LEN;cbn[length];lia. }
 destruct(allocated_validation_storage _ VALID SOURCECOUNT)as[initial[before[fields[output[argv[all H]]]]]].
 destruct H as[INIT[OLD[BYTES[SPAN[OWN[ASEP[SEP[SPACE[WRITE[LITERALS[POLICY[FSEP[OSEP[FLIT OLIT]]]]]]]]]]]]]].
 destruct(split_guest_bytes all textfields(bytes::export_bytes::tree_bytes::stdin_bytes::sources)BYTES)as[numbers[tail[ALL[NUMBYTES TAILBYTES]]]].
 subst all;assert(LNUM:length numbers=10%nat)by(rewrite<-LEN,<-NUMBYTES,length_map;reflexivity).
 destruct tail as[|p tail];[discriminate TAILBYTES|].
 destruct tail as[|export tail];[discriminate TAILBYTES|].
 destruct tail as[|tree tail];[discriminate TAILBYTES|].
 destruct tail as[|stdin tail];[discriminate TAILBYTES|].
 destruct tail as[|x rest].
 { cbn in TAILBYTES;injection TAILBYTES as A B C D EMPTY;subst sources;cbn in NONEMPTY;lia. }
 change(guest_bytes p::guest_bytes export::guest_bytes tree::guest_bytes stdin::map guest_bytes(x::rest)=
 bytes::export_bytes::tree_bytes::stdin_bytes::sources)in TAILBYTES.
 injection TAILBYTES as PB EB TB SB GB.
 assert(SIZE:length(x::rest)=length sources)by(rewrite<-GB;cbn;rewrite length_map;reflexivity).
 destruct(guest_arguments_split _ _ _ _ _ _ OWN)as[NUMOWN TAILOWN].
 rewrite LNUM in TAILOWN;change(guest_arguments_owned before argv Ptrofs.zero 12(p::export::tree::stdin::x::rest))in TAILOWN.
 destruct TAILOWN as[PO[PL[EO[EL[TO[TL[SO[SL GUEST]]]]]]]].
 apply Forall_app in SEP;destruct SEP as[NUMSEP TAILSEP].
 pose proof(Forall_inv TAILSEP)as PSEP;pose proof(Forall_inv_tail TAILSEP)as R1.
 pose proof(Forall_inv R1)as ESEP;pose proof(Forall_inv_tail R1)as R2.
 pose proof(Forall_inv R2)as TSEP;pose proof(Forall_inv_tail R2)as R3.
 pose proof(Forall_inv R3)as SSEP;pose proof(Forall_inv_tail R3)as GSEP.
 assert(SPAN':guest_table_span Ptrofs.zero(16+Z.of_nat(length sources))).
 { assert(ALLLEN:length(numbers++p::export::tree::stdin::x::rest)=(14+length sources)%nat).
   { rewrite length_app,LNUM;change(10+(4+length(x::rest))=14+length sources)%nat;lia. }
   rewrite ALLLEN,Nat2Z.inj_add in SPAN;change(guest_table_span Ptrofs.zero(2+(14+Z.of_nat(length sources))))in SPAN;replace(2+(14+Z.of_nat(length sources)))with(16+Z.of_nat(length sources))in SPAN by lia;exact SPAN. }
 assert(NUMWIDTH:Forall(fun arg=>address_block(guest_pointer arg)<>main_policy_block)numbers).
 { eapply Forall_impl;[|exact NUMSEP];intros arg[SETUP[A B]];exact(proj1(proj2 SETUP)). }
 assert(NUMENTRY:numeric_entry_buffers before fields argv Ptrofs.zero(map guest_numeric numbers)).
 { destruct ASEP as[SETUP[AF AO]];destruct SPACE as[FRANGE OUTPUT].
   split;[exact(proj1(proj2 FSEP))|];split;[exact(proj1(proj2 SETUP))|];split;[exact AF|];split.
   - destruct SPAN' as[C B];change(Ptrofs.unsigned Ptrofs.zero)with 0 in B|-*;lia.
   - split.
     + apply Forall_map;eapply Forall_impl;[|exact NUMSEP];intros arg[GLOBAL[A B]];exact A.
     + split;[exact(guest_numeric_ready before argv Ptrofs.zero 0 numbers NUMWIDTH NUMOWN)|];split;assumption. }
 assert(NGUEST:Forall(fun arg=>numeric_separate fields(address_block(guest_pointer arg)))(x::rest)).
 { eapply Forall_impl;[|exact GSEP];intros arg SEP;apply validation_separate_numeric with(output:=output);exact SEP. }
 assert(PGUEST:Forall(fun arg=>address_block(guest_pointer arg)<>output)(x::rest)).
 { eapply Forall_impl;[|exact GSEP];intros arg[A[B C]];exact C. }
 assert(SGUEST:Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))(x::rest)).
 { eapply Forall_impl;[|exact GSEP];intros arg[A[B C]];exact A. }
 destruct WRITE as[PF[FW[TW[SW AW]]]].
 destruct(numeric_validation_source cell(validation_locals fields output)(argument_witness_env argv(16+Z.of_nat(length sources)))before Kstop
 fields(map guest_numeric numbers)(16+Z.of_nat(length sources))argv Ptrofs.zero(guest_pointer p)bytes output
 (guest_pointer export)(guest_pointer tree)(guest_pointer stdin)export_bytes tree_bytes stdin_bytes x rest
 ltac:(rewrite length_map;exact LNUM)NUMENTRY(validation_numeric_locals fields output)
 (validation_separate_numeric _ _ _ PSEP)(validation_separate_numeric _ _ _ ESEP)
 (validation_separate_numeric _ _ _ TSEP)(validation_separate_numeric _ _ _ SSEP)NGUEST FLIT
 ltac:(unfold validation_locals;WriteAll.lookup)ltac:(intros _;unfold validation_locals;WriteAll.lookup)
 ltac:(unfold validation_locals;WriteAll.lookup)PL
 ltac:(apply parent_string_input;rewrite<-PB;exact PO)(proj2 SPACE)
 (proj2(proj2 ASEP))(proj2(proj2 ESEP))(proj2(proj2 TSEP))(proj2(proj2 SSEP))PGUEST
 ltac:(intro EQ;apply(proj1(proj2 OSEP));symmetry;exact EQ)OLIT
 ltac:(lia)ltac:(lia)SPAN' GUEST(proj1 ASEP)SGUEST(proj1 TSEP)(proj1 SSEP)LITERALS
 ltac:(unfold validation_locals;WriteAll.lookup)ltac:(unfold validation_locals;WriteAll.lookup)
 ltac:(unfold validation_locals;WriteAll.lookup)ltac:(unfold validation_locals;WriteAll.lookup)
 ltac:(unfold validation_locals;WriteAll.lookup)ltac:(unfold validation_locals;WriteAll.lookup)
 ltac:(unfold validation_locals;WriteAll.lookup)ltac:(unfold validation_locals;WriteAll.lookup)
 ltac:(unfold validation_locals;WriteAll.lookup)ltac:(unfold validation_locals;WriteAll.lookup)
 ltac:(unfold validation_locals;WriteAll.lookup)
 ltac:(unfold argument_witness_env;WriteAll.lookup)ltac:(unfold argument_witness_env;WriteAll.lookup)
 EL TL SL ltac:(rewrite<-EB;exact EO)ltac:(rewrite<-TB;exact TO)ltac:(rewrite<-SB;exact SO)FW TW SW AW)
 as[initialized[numeric_count[numeric[final[FIELDS[STORES[FRAME GUARANTEE]]]]]]].
 exists initial,before,fields,output,argv,(map guest_numeric numbers),(guest_pointer export),(guest_pointer tree),(guest_pointer stdin),x,rest,initialized,numeric_count,numeric,final.
 split;[exact INIT|];split;[exact OLD|];split.
 - rewrite map_map;exact NUMBYTES.
 - split;[exact GB|];split;[exact FIELDS|];split;[exact STORES|];split;assumption.
Qed.
