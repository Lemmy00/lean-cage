(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Imported acceptance controls the actual full-helper source endpoint. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Deterministic StoreSteps.
From LeanImport Require Import Lean.
From LeanCageBounds Require Import BoundsImport BoundsImportedValues BoundsImported.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsStructure BoundsMemory BoundsSource.
Local Close Scope lean_scope.
Open Scope Z_scope.
Import ListNotations.
Theorem bounds_imported_execution e le m argc bytes fields :
 17<=bound_nat argc<=2147483647 -> bound_nat bytes<=Int64.max_unsigned ->
 le!_argc=Some(Vint(Int.repr(bound_nat argc))) ->
 le!_bytes=Some(Vlong(Int64.repr(bound_nat bytes))) ->
 e!_policy__1=None -> policy_image m(bound_values fields) ->
 exists count final,(count<=140)%nat /\ forall cell k,
 steps main_ge cell(live(State f_main bounds_region k e le m))
 (repeat(source_step E0)count)
 (live(bounds_endpoint e final k m(negb(bound_bool(LeanCageM4_Bounds_nativeBounds argc bytes fields))))) /\
 (forall events target,steps main_ge cell(live(State f_main bounds_region k e le m))events target ->
 (length events<=count)%nat -> routine_memory target=m) /\
 (forall events state,steps main_ge cell(live(State f_main bounds_region k e le m))events(live state) ->
 (length events<count)%nat -> exists next,step main_ge cell(live state)(source_step E0)(live next)) /\
 (forall events state,steps main_ge cell(live(State f_main bounds_region k e le m))events(live state) ->
 length events=count -> state=bounds_endpoint e final k m
  (negb(bound_bool(LeanCageM4_Bounds_nativeBounds argc bytes fields)))) /\
 (forall n,(n<=count)%nat ->steps main_ge cell(live(State f_main bounds_region k e le m))
  (repeat(source_step E0)n++[loss_step])(dead m)).
Proof.
 intros COUNT BYTES ARGC TOTAL GLOBAL IMAGE.
 rewrite (imported_bounds_exact argc bytes fields ltac:(lia)(proj1 IMAGE));rewrite negb_involutive.
 apply bounds_region_execution;[exact COUNT|pose proof(bound_nat_nonnegative bytes);lia|
 exact ARGC|exact TOTAL|exact GLOBAL|exact IMAGE].
Qed.
