(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Selected endpoints precede the next out-of-slice call. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure MainControl.
From LeanCageBounds Require Import BoundsStructure BoundsMemory BoundsSource.
From LeanCageArguments Require Import ArgumentStructure ArgumentControl ArgumentWords ArgumentMemory ArgumentBounds.
From LeanCageValidation Require Import ValidationStructure ValidationValues ValidationFinish ExportCaller DigestCaller ExecutableCaller ValidationComposition.
From LeanCageInitialization Require Import DigestArguments InitializationSource.
From LeanCageParent Require Import ParentStructure ParentFinish ParentFrontier ParentTrace TraceRegion TraceInitialization TraceCut.
Import ListNotations.

Lemma selected_skip_shape f k e le m : selected_stop_shape(State f Sskip k e le m).
Proof. repeat eexists;left;reflexivity. Qed.
Lemma selected_report_shape f opt ty args k e le m :
 selected_stop_shape(State f(Scall opt(Evar _result_of ty)args)k e le m).
Proof. repeat eexists;right;repeat eexists. Qed.

Lemma selected_selection_rejection index e le k m s :
 (index=15 \/index=16 \/index=20 \/index=22)%nat->
 selection_frontier index e le k m true s->selected_stop_shape s.
Proof.
 intros[INDEX|[INDEX|[INDEX|INDEX]]][final[FRAME EQ]];subst index;subst s;
 apply selected_report_shape.
Qed.

Lemma selected_argument_bounds argc inputs values e le k m :
 selected_stop_shape(argument_bounds_endpoint argc inputs values e le k m).
Proof.
 unfold argument_bounds_endpoint;destruct(argument_scan 16 0 inputs)as[total|index total].
 - unfold bounds_endpoint;destruct(bounds_rejected argc total values).
   + apply selected_report_shape.
   + apply selected_skip_shape.
 - apply selected_report_shape.
Qed.

Theorem traced_frontier_selected middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values history s :
 traced_initialization_frontier middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values history s->
 selected_stop_shape s.
Proof.
 intros[[TRACE[REJECT OBS]]|[MATCH INIT]].
 - destruct REJECT as[FRONT[final EQ]];subst s;apply selected_report_shape.
 - unfold initialization_frontier in INIT;destruct(export_bad export_bytes).
   + eapply selected_selection_rejection;[right;left;reflexivity|exact INIT].
   + unfold digest_arguments_frontier in INIT;destruct(digest_pair_bad tree_bytes stdin_bytes).
     * eapply selected_selection_rejection;[right;right;left;reflexivity|exact INIT].
     * unfold executable_bounds_frontier in INIT;destruct(executable_bad(guest_bytes x)).
       -- eapply selected_selection_rejection;[right;right;right;reflexivity|exact INIT].
       -- destruct INIT as[final EQ];subst s;apply selected_argument_bounds.
Qed.

Lemma numeric_rejection_selected e le k m (history:list int) s :
 history=[] /\s=numeric_failure_state e le k m->selected_stop_shape s.
Proof. intros[H EQ];subst s;apply selected_report_shape. Qed.

Theorem traced_frontier_accepted_history middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values
 history k' e' le' m' :
 traced_initialization_frontier middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values
 history(State f_main Sskip(Kseq after_bounds k')e' le' m')->matching_history bytes history.
Proof.
 intros[[TRACE[[_[final EQ]]OBS]]|[MATCH INIT]];[discriminate EQ|exact MATCH].
Qed.

Theorem residual_acceptance_history cell P middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values
 n history k' e' le' m' :
 trace_certificate main_ge cell P
 (traced_initialization_frontier middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values)
 n history(State f_main Sskip(Kseq after_bounds k')e' le' m')->matching_history bytes history.
Proof.
 intros CERT;eapply traced_frontier_accepted_history.
 eapply trace_post_bounds_cut;[intros h s END;eapply traced_frontier_selected;exact END|exact CERT].
Qed.
