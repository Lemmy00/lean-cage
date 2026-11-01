(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Exact acceptance/rejection boundaries and all finite prefixes. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine Deterministic ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure MainPrefix.
From LeanCageBounds Require Import BoundsStructure BoundsMemory BoundsControl BoundsSequence.
Import ListNotations.
Open Scope Z_scope.
Definition bounds_failure_state e le k m := State f_main bounds_report
 (Kseq bounds_report_suffix(Kseq bounds_failure_return k))e le m.
Definition bounds_endpoint e le k m (bad:bool) := if bad then bounds_failure_state e le k m
 else State f_main Sskip k e le m.
Lemma bounds_finish_source e le m k bad : le!_t'55=Some(Val.of_bool bad) ->
 store_path main_ge(fun after=>after=m)(State f_main bounds_finish k e le m)
 (if bad then 3%nat else 1%nat)(bounds_endpoint e le k m bad).
Proof.
 intros REG;rewrite(proj1(proj2(proj2 bounds_exact_structure))).
 destruct bad;unfold bounds_endpoint,bounds_failure_state;bounds_next.
 - eapply certified_if_edge with(v:=Val.of_bool true)(b:=true);
   [apply old_expression_value;apply value_temp;exact REG|reflexivity].
 - rewrite(proj2(proj2(proj2 bounds_exact_structure))).
   bounds_route;bounds_route;apply store_done;reflexivity.
 - eapply certified_if_edge with(v:=Val.of_bool false)(b:=false);
   [apply old_expression_value;apply value_temp;exact REG|reflexivity].
 - apply store_done;reflexivity.
Qed.
Theorem bounds_region_source e le m argc bytes values :
 17<=argc<=2147483647 -> 0<=bytes<=Int64.max_unsigned ->
 le!_argc=Some(Vint(Int.repr argc)) -> le!_bytes=Some(Vlong(Int64.repr bytes)) ->
 e!_policy__1=None -> policy_image m values ->
 exists count final,(count<=140)%nat /\
 (forall k,store_path main_ge(fun after=>after=m)(State f_main bounds_region k e le m)count
  (bounds_endpoint e final k m(bounds_rejected argc bytes values))).
Proof.
 intros COUNT BYTES ARGC TOTAL GLOBAL IMAGE.
 destruct(bounds_conditions_source e le m argc bytes values COUNT BYTES ARGC TOTAL GLOBAL IMAGE)
 as[n[final[BOUND[PATH REG]]]].
 exists(n+2+(if bounds_rejected argc bytes values then 3 else 1))%nat,final.
 split;[destruct(bounds_rejected argc bytes values);cbn;lia|]. intros k.
 change bounds_region with(Ssequence bounds_conditions bounds_finish).
 replace(n+2+(if bounds_rejected argc bytes values then 3 else 1))%nat
 with(S(n+S(if bounds_rejected argc bytes values then 3 else 1)))%nat by lia.
 bounds_route;eapply store_path_trans;[apply PATH|].
 bounds_route;apply bounds_finish_source;exact REG.
Qed.
Theorem bounds_region_execution e le m argc bytes values :
 17<=argc<=2147483647 -> 0<=bytes<=Int64.max_unsigned ->
 le!_argc=Some(Vint(Int.repr argc)) -> le!_bytes=Some(Vlong(Int64.repr bytes)) ->
 e!_policy__1=None -> policy_image m values ->
 exists count final,(count<=140)%nat /\ forall cell k,
 steps main_ge cell(live(State f_main bounds_region k e le m))
 (repeat(source_step E0)count)(live(bounds_endpoint e final k m(bounds_rejected argc bytes values))) /\
 (forall events target,steps main_ge cell(live(State f_main bounds_region k e le m))events target ->
  (length events<=count)%nat -> routine_memory target=m) /\
 (forall events state,steps main_ge cell(live(State f_main bounds_region k e le m))events(live state) ->
  (length events<count)%nat -> exists next,step main_ge cell(live state)(source_step E0)(live next)) /\
 (forall events state,steps main_ge cell(live(State f_main bounds_region k e le m))events(live state) ->
  length events=count -> state=bounds_endpoint e final k m(bounds_rejected argc bytes values)) /\
 (forall n,(n<=count)%nat ->
  steps main_ge cell(live(State f_main bounds_region k e le m))
   (repeat(source_step E0)n++[loss_step])(dead m)).
Proof.
 intros COUNT BYTES ARGC TOTAL GLOBAL IMAGE.
 destruct(bounds_region_source e le m argc bytes values COUNT BYTES ARGC TOTAL GLOBAL IMAGE)
 as[count[final[BOUND PATH]]]. exists count,final;split;[exact BOUND|]. intros cell k.
 split;[eapply store_path_actual;apply PATH|].
 split;[intros events target RUN LEN;eapply store_path_bounded_memory;[apply PATH|exact RUN|exact LEN]|].
 split;[intros events state RUN LEN;eapply store_path_bounded_progress;[apply PATH|exact RUN|exact LEN]|].
 split;[intros events state RUN LEN;eapply store_path_bounded_endpoint;[apply PATH|exact RUN|exact LEN]|].
 intros n N;destruct(store_path_loss_every_prefix _ cell _ _ _ _ n(PATH k)N)
 as[mid[LIVE[LOST SAME]]];cbn in SAME;rewrite SAME in LOST;exact LOST.
Qed.
