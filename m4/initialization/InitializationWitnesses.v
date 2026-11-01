(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine Library FreshMemoryDraft WriteAll.
From LeanCageMain Require Import Main MainStructure MainMemory.
From LeanCageBounds Require Import BoundsMemory BoundsStructure BoundsSource.
From LeanCageArguments Require Import StringMachine ArgumentMemory ArgumentAllocation ArgumentWitnesses
 ArgumentStructure ArgumentControl ArgumentBounds ArgumentWords.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import StringRegion StringSource ValidationStructure ValidationValues
 ValidationFinish ValidationAllocation ValidationComposition DigestCaller ExportCaller ExecutableCaller.
From LeanCageInitialization Require Import StoreFrames ConfigurationMemory DigestArguments InitializationSource InitializationAllocation.
Import ListNotations.
Open Scope Z_scope.
Inductive initialization_result :=
 | rejected_export | rejected_digest | rejected_executable
 | rejected_argument(index total:Z) | rejected_policy(total:Z) | initialization_ready(total:Z).
Definition initialization_result_of export tree stdin sources values :=
 if export_bad export then rejected_export else
 if digest_pair_bad tree stdin then rejected_digest else
 if executable_bad(hd [] sources)then rejected_executable else
 match argument_scan_bytes 16 0 sources with
 |arguments_rejected index total=>rejected_argument index total
 |arguments_accepted total=>if bounds_rejected(16+Z.of_nat(length sources))total values
 then rejected_policy total else initialization_ready total end.
Definition initialization_error index e final k m := State f_main(selection_report index)
 (Kseq(selection_report_rest index)(Kseq(selection_return index)(Kseq(selection_after index)k)))e final m.
Definition initialization_result_state result before configured after e final k :=
 match result with
 |rejected_export=>initialization_error 16 e final k before
 |rejected_digest=>initialization_error 20 e final k configured
 |rejected_executable=>initialization_error 22 e final k after
 |rejected_argument _ _=>argument_failure_state e final(Kseq after_arguments k)after
 |rejected_policy _=>bounds_endpoint e final(Kseq after_bounds k)after true
 |initialization_ready _=>bounds_endpoint e final(Kseq after_bounds k)after false end.
Lemma initialization_bytes_result before configured after e le k argc export tree stdin x rest values sources s :
 map guest_bytes(x::rest)=sources->argc=16+Z.of_nat(length sources)->
 initialization_frontier before configured after e le k argc export tree stdin x rest values s->
 exists final,s=initialization_result_state(initialization_result_of export tree stdin sources values)
 before configured after e final k.
Proof.
 intros BYTES COUNT END;subst sources argc;rewrite length_map in *.
 unfold initialization_frontier,initialization_result_of in *;rewrite length_map.
 destruct(export_bad export);[destruct END as[final[FRAME LAST]];exists final;exact LAST|].
 unfold digest_arguments_frontier in END;destruct(digest_pair_bad tree stdin);
 [destruct END as[final[FRAME LAST]];exists final;exact LAST|].
 change(hd [] (map guest_bytes(x::rest)))with(guest_bytes x);unfold executable_bounds_frontier in END;destruct(executable_bad(guest_bytes x));
 [destruct END as[final[FRAME LAST]];exists final;exact LAST|].
 destruct END as[final LAST];exists final;unfold argument_bounds_endpoint in LAST.
 rewrite argument_scan_representation in LAST.
 destruct(argument_scan_bytes 16 0(map guest_bytes(x::rest)))as[total|index total]eqn:SCAN.
 - destruct(bounds_rejected(16+Z.of_nat(length(x::rest)))total values);exact LAST.
 - exact LAST.
Qed.
Theorem allocated_initialization_certificate cell export_bytes tree_bytes stdin_bytes sources values :
 admissible_guest_sources sources->digest_input_admissible export_bytes->
 digest_input_admissible tree_bytes->digest_input_admissible stdin_bytes->
 length values=10%nat->Forall(fun v=>0<=v<=Int64.max_unsigned)values->
 exists initial numeric before argv flagged tree_set configured after tree stdin,
 Genv.init_mem Main.prog=Some initial /\policy_stores main_policy_block 0 initial values numeric /\old_memory numeric before /\
 configuration_stores before flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.repr 128))=Some after /\
 region_certificate main_ge cell(initialization_prefix before flagged tree_set configured after)
 (fun s=>exists final,s=initialization_result_state(initialization_result_of export_bytes tree_bytes stdin_bytes sources values)
 before configured after empty_env final Kstop)
 (26*length sources+4540)(State f_main(validation_suffix 16)Kstop empty_env
 (argument_witness_env argv(16+Z.of_nat(length sources)))before).
Proof.
 intros[NONEMPTY[COUNT GUEST]]EXPORT TREE STDIN LEN RANGE.
 assert(VALID:Forall digest_input_admissible(export_bytes::tree_bytes::stdin_bytes::sources)).
 { constructor;[exact EXPORT|];constructor;[exact TREE|];constructor;assumption. }
 destruct(allocated_setup_inputs values(export_bytes::tree_bytes::stdin_bytes::sources)LEN RANGE VALID ltac:(cbn;lia))
 as[initial[numeric[before[argv[inputs[INIT[STORES[OLD[BYTES[SPAN[ARGS[ARGVSEP[SEP[IMAGE[LITERALS WRITE]]]]]]]]]]]]]]].
 destruct inputs as[|export inputs];[discriminate BYTES|].
 destruct inputs as[|tree inputs];[discriminate BYTES|].
 destruct inputs as[|stdin inputs];[discriminate BYTES|].
 destruct inputs as[|x rest].
 { cbn in BYTES;inversion BYTES;subst sources;cbn in NONEMPTY;lia. }
 change(guest_bytes export::guest_bytes tree::guest_bytes stdin::map guest_bytes(x::rest)=
 export_bytes::tree_bytes::stdin_bytes::sources)in BYTES.
 injection BYTES as EB TB SB GUESTBYTES.
 assert(SIZE:length(x::rest)=length sources)by(rewrite<-GUESTBYTES;cbn;rewrite length_map;reflexivity).
 destruct ARGS as[EO[EL[TO[TL[SO[SL OWN]]]]]].
 pose proof(Forall_inv_tail SEP)as MORE;pose proof(Forall_inv MORE)as TSEP;
 pose proof(Forall_inv_tail MORE)as MORE2;pose proof(Forall_inv MORE2)as SSEP;
 pose proof(Forall_inv_tail MORE2)as GSEP.
 destruct WRITE as[PW[FW[TW[SW AW]]]].
 assert(SPAN':guest_table_span Ptrofs.zero(16+Z.of_nat(length sources))).
 { assert (LENGTH : length (export :: tree :: stdin :: x :: rest) = (3 + length sources)%nat).
   { change (3 + length (x :: rest) = 3 + length sources)%nat;rewrite SIZE;reflexivity. }
   rewrite LENGTH,Nat2Z.inj_add in SPAN.
   change (guest_table_span Ptrofs.zero (13 + (3 + Z.of_nat(length sources)))) in SPAN.
   replace (13 + (3 + Z.of_nat(length sources))) with (16 + Z.of_nat(length sources)) in SPAN by lia;exact SPAN. }
 destruct(initialization_certificate cell empty_env(argument_witness_env argv(16+Z.of_nat(length sources)))before Kstop
 (16+Z.of_nat(length sources))argv Ptrofs.zero(guest_pointer export)(guest_pointer tree)(guest_pointer stdin)
 export_bytes tree_bytes stdin_bytes x rest values
 ltac:(lia)ltac:(lia)SPAN' OWN ARGVSEP GSEP TSEP SSEP IMAGE LITERALS
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 ltac:(unfold argument_witness_env;WriteAll.lookup)ltac:(unfold argument_witness_env;WriteAll.lookup)
 EL TL SL ltac:(rewrite<-EB;exact EO)ltac:(rewrite<-TB;exact TO)ltac:(rewrite<-SB;exact SO)FW TW SW AW)
 as[flagged[tree_set[configured[after[CONFIG[STORE CERT]]]]]].
 exists initial,numeric,before,argv,flagged,tree_set,configured,after,(guest_pointer tree),(guest_pointer stdin).
 split;[exact INIT|];split;[exact STORES|];split;[exact OLD|];split;[exact CONFIG|];split.
 - rewrite Ptrofs.add_zero_l in STORE;exact STORE.
 - rewrite SIZE in CERT;eapply AssemblyRegions.region_convert;[exact CERT|intros;assumption|].
   intros endpoint END;eapply initialization_bytes_result;[exact GUESTBYTES|reflexivity|exact END].
Qed.
