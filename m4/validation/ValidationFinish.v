(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationCalls.
Import ListNotations.
Open Scope nat_scope.
Definition selection_frontier index e before k m(bad:bool)s := exists final,validation_frame before final /\
 s=if bad then State f_main(selection_report index)
 (Kseq(selection_report_rest index)(Kseq(selection_return index)(Kseq(selection_after index)k)))e final m
 else State f_main(selection_after index)k e final m.
Lemma selection_finish_certificate cell index result bad e before le m k :
 selection_shape index result->le!result=Some(Val.of_bool bad)->validation_frame before le->
 region_certificate main_ge cell(fun after=>after=m)(selection_frontier index e before k m bad)4
 (State f_main Sskip(Kseq(selection_finish index)(Kseq(selection_after index)k))e le m).
Proof.
 intros[SHAPE FAILURE]REG FRAME;validation_route;rewrite SHAPE;destruct bad.
 - validation_next.
   + eapply certified_if_edge with(v:=Val.of_bool true)(b:=true);
     [apply old_expression_value;apply value_temp;exact REG|reflexivity].
   + rewrite FAILURE;validation_route;validation_route;apply region_stop;[reflexivity|exists le;auto].
 - validation_next.
   + eapply certified_if_edge with(v:=Val.of_bool false)(b:=false);
     [apply old_expression_value;apply value_temp;exact REG|reflexivity].
   + validation_route;apply region_stop;[reflexivity|exists le;auto].
Qed.
