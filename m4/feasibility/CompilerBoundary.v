(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.machine: State the exact missing stock-semantics producer for parent observations. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Integers AST Values Memory Events Globalenvs Clight.
Require Import Machine LibraryMachine.
From LeanCageArguments Require Import StringMachine.
From LeanCageParent Require Import ParentMachine ParentRuns.
Import ListNotations.

Definition parent_external_compatibility (ge:genv) := forall m value,exists trace,
 external_call(EF_external "getppid"(mksignature [] Xint cc_default))(Genv.to_senv ge) [] m trace(Vint value)m.
Definition parent_observation_projection ge := forall cell k m value,
 parent_step ge cell(live(Callstate getppid_definition [] k m))(parent_observed value)
  (live(Returnstate(Vint value)k m))->
 exists trace,Clight.step2 ge(Callstate getppid_definition [] k m)trace(Returnstate(Vint value)k m).
Definition parent_external_safety (ge:genv) := forall m trace result after,
 external_call(EF_external "getppid"(mksignature [] Xint cc_default))(Genv.to_senv ge) [] m trace result after->
 after=m /\exists value,result=Vint value.

Theorem stock_parent_step_exact ge k m value trace :
 Clight.step2 ge(Callstate getppid_definition [] k m)trace(Returnstate(Vint value)k m)<->
 external_call(EF_external "getppid"(mksignature [] Xint cc_default))(Genv.to_senv ge) [] m trace(Vint value)m.
Proof.
 split;intros STEP.
 - inversion STEP;subst;assumption.
 - apply Clight.step_external_function;exact STEP.
Qed.

Theorem parent_projection_iff_external_contract ge :
 parent_observation_projection ge<->parent_external_compatibility ge.
Proof.
 split.
 - intros PROJECT m value.
   set(cell:={|tls_block:=1%positive;tls_offset:=0%Z|}).
   assert(LOCAL:parent_step ge cell(live(Callstate getppid_definition [] Kstop m))(parent_observed value)
    (live(Returnstate(Vint value)Kstop m)))by constructor.
   destruct(PROJECT cell Kstop m value LOCAL)as[trace STEP].
   exists trace;apply(stock_parent_step_exact ge Kstop m value trace);exact STEP.
 - intros COMPAT cell k m value LOCAL;destruct(COMPAT m value)as[trace EXTERNAL].
   exists trace;apply stock_parent_step_exact;exact EXTERNAL.
Qed.

Theorem delegated_parent_step_projects ge cell start next :
 parent_step ge cell(live start)parent_internal(live next)->Clight.step2 ge start E0 next.
Proof.
 intros STEP;unfold parent_internal,string_source in STEP.
 inversion STEP;subst;match goal with H:string_step _ _ _ _ _|-_=>inversion H;subst end.
 match goal with H:library_step _ _ _ _ _|-_=>inversion H;subst end.
 match goal with H:Machine.step _ _ _ _ _|-_=>inversion H;subst end;assumption.
Qed.

Theorem stock_internal_refines_parent ge cell start next :
 internal_state start->Clight.step2 ge start E0 next->
 parent_step ge cell(live start)parent_internal(live next).
Proof.
 intros INSIDE STEP;unfold parent_internal,string_source.
 apply ParentMachine.previous_step;apply StringMachine.previous_step;apply original_step.
 apply internal;assumption.
Qed.

Theorem stock_parent_refines_local_under_effect_contract ge : parent_external_safety ge->
 forall cell k m trace result after,
 Clight.step2 ge(Callstate getppid_definition [] k m)trace(Returnstate result k after)->
 exists value,result=Vint value /\after=m /\
 parent_step ge cell(live(Callstate getppid_definition [] k m))(parent_observed value)
 (live(Returnstate result k after)).
Proof.
 intros SAFE cell k m trace result after STEP.
 assert(EXTERNAL:external_call(EF_external "getppid"(mksignature [] Xint cc_default))(Genv.to_senv ge) [] m trace result after).
 { inversion STEP;subst;assumption. }
 destruct(SAFE _ _ _ _ EXTERNAL)as[MEM[value RESULT]];subst after result.
 exists value;split;[reflexivity|];split;[reflexivity|constructor].
Qed.
