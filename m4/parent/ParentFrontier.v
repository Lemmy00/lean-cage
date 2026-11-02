(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import ValidationStructure ValidationValues ValidationFinish ExportCaller.
From LeanCageInitialization Require Import InitializationSource DigestArguments ArgumentsInitialization.
From LeanCageParent Require Import ParentStructure ParentFinish ParentControl ParentAfterParse.
Import ListNotations.
Open Scope nat_scope.
Definition parent_rejection e le k m parsed s := parent_frontier e le k m parsed s /\
 exists final,s=parent_endpoint e final k m true.
Definition parent_admission e le k m parsed s := parent_frontier e le k m parsed s /\
 exists final,validation_frame le final /\s=State f_main(validation_suffix 16)k e final m.
Theorem parent_frontier_split e le k m parsed s : parent_frontier e le k m parsed s->
 parent_rejection e le k m parsed s \/parent_admission e le k m parsed s.
Proof.
 intros ORIGINAL;pose proof ORIGINAL as END;unfold parent_frontier in END;destruct(parent_guard_bad parsed).
 - destruct END as[final[FRAME LAST]];left;split;[exact ORIGINAL|eexists;exact LAST].
 - destruct END as[observed[final[FRAME[REG LAST]]]];destruct(negb(Int.eq observed(Int.repr(parent_value parsed)))).
   + left;split;[exact ORIGINAL|eexists;exact LAST].
   + right;split;[exact ORIGINAL|];exists final;split;[exact FRAME|exact LAST].
Qed.
Lemma initialization_frame before configured after e le mid k argc export_bytes tree_bytes stdin_bytes x rest values s :
 validation_frame le mid->
 initialization_frontier before configured after e mid k argc export_bytes tree_bytes stdin_bytes x rest values s->
 initialization_frontier before configured after e le k argc export_bytes tree_bytes stdin_bytes x rest values s.
Proof.
 intros FRAME END;unfold initialization_frontier in *;destruct(export_bad export_bytes).
 - destruct END as[final[MORE LAST]];exists final;split;[eapply validation_frame_trans;eassumption|exact LAST].
 - eapply digest_arguments_frame;eassumption.
Qed.
