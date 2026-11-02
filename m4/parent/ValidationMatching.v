(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine Library FreshMemoryDraft ScalarMemory WriteAll.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainFields MainEntry MainSource MainOutcomes.
From LeanCageArguments Require Import ArgumentMemory ArgumentWitnesses.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues ValidationAllocation.
From LeanCageInitialization Require Import StoreFrames ConfigurationMemory InitializationAllocation InitializationSource InitializationWitnesses.
From LeanCageParent Require Import ParentMemory ParentAllocation ParentMachine NumericMemory NumericComposition NumericMatching
 ValidationLocals ValidationAllocation ValidationInputs InputRepresentation TraceRegion.
Import ListNotations.
Open Scope Z_scope.
Theorem allocated_validation_matching cell textfields bytes export_bytes tree_bytes stdin_bytes sources value :
 fields_complete textfields=true->decimal_number bytes=Some value->(0<value<=2147483647)%Z->
 length textfields=10%nat->Forall digest_input_admissible textfields->
 digest_input_admissible bytes->digest_input_admissible export_bytes->digest_input_admissible tree_bytes->digest_input_admissible stdin_bytes->
 admissible_guest_sources sources->
 exists initial before fields output argv inputs export x rest initialized numeric middle flagged tree_set configured after tree stdin events final,
 Genv.init_mem Main.prog=Some initial /\old_memory initial before /\
 validation_input_representation before fields argv textfields bytes export_bytes tree_bytes stdin_bytes sources
 inputs export tree stdin x rest /\
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(field_values textfields)numeric /\
 number_post numeric output Ptrofs.zero(decimal_number bytes)middle /\
 configuration_stores middle flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.repr 128))=Some after /\
 parent_steps main_ge cell(live(State f_main numeric_region Kstop(validation_locals fields output)
 (argument_witness_env argv(16+Z.of_nat(length sources)))before))events
 (live(initialization_result_state(initialization_result_of export_bytes tree_bytes stdin_bytes sources(field_values textfields))
 middle configured after(validation_locals fields output)final Kstop)) /\observations events=[Int.repr value].
Proof.
 intros COMPLETE PARSED PIDRANGE LEN NUMVALID PVALID EVALID TVALID SVALID[NONEMPTY[COUNT GUESTVALID]].
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
 assert(NCOMPLETE:numeric_complete(map guest_numeric numbers)=true).
 { rewrite numeric_complete_data,map_map;change(fields_complete(map guest_bytes numbers)=true);rewrite NUMBYTES;exact COMPLETE. }
 assert(NVALUES:numeric_values(map guest_numeric numbers)=field_values textfields).
 { rewrite numeric_values_data,map_map;change(field_values(map guest_bytes numbers)=field_values textfields);rewrite NUMBYTES;reflexivity. }
 destruct(numeric_validation_matching cell(validation_locals fields output)(argument_witness_env argv(16+Z.of_nat(length sources)))before Kstop
 fields(map guest_numeric numbers)(16+Z.of_nat(length sources))argv Ptrofs.zero(guest_pointer p)bytes output
 (guest_pointer export)(guest_pointer tree)(guest_pointer stdin)export_bytes tree_bytes stdin_bytes x rest value
 NCOMPLETE PARSED PIDRANGE
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
 as[initialized[numeric[middle[flagged[tree_set[configured[after[events[endpoint[FIELDS[STORES[POST[CONFIG[STORE[RUN[END OBS]]]]]]]]]]]]]]]].
 rewrite NVALUES in STORES,END.
 destruct(initialization_bytes_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GB eq_refl END)as[final LAST];subst endpoint.
 exists initial,before,fields,output,argv,(map guest_numeric numbers),(guest_pointer export),x,rest,initialized,numeric,middle,flagged,tree_set,configured,after,
 (guest_pointer tree),(guest_pointer stdin),events,final.
 split;[exact INIT|];split;[exact OLD|];split.
 - exists numbers,p,export,tree,stdin.
   split;[exact NUMBYTES|];split;[exact PB|];split;[exact EB|];split;[exact TB|];split;[exact SB|].
   split;[exact GB|];split;[reflexivity|];split;[reflexivity|];split;[reflexivity|];split;[reflexivity|].
   split;[exact OWN|exact NUMENTRY].
 - split;[exact FIELDS|];split;[exact STORES|];split;[exact POST|];split;[exact CONFIG|];split.
   + rewrite Ptrofs.add_zero_l in STORE;exact STORE.
   + split;[exact RUN|exact OBS].
Qed.
