(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Compose every actual short-circuit guard with a finite bound. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsStructure BoundsMemory BoundsControl.
Import ListNotations.
Open Scope Z_scope.
Fixpoint guard_links id guards := match guards with
 | []=>True | g::rest=>guard_input g=id /\ guard_links(guard_output g)rest end.
Fixpoint final_guard_id id guards := match guards with
 | []=>id | g::rest=>final_guard_id(guard_output g)rest end.
Definition guard_results values guards := existsb(fun g=>guard_bad g(nth(Z.to_nat(guard_index g))values 0))guards.
Theorem policy_guard_links : guard_links _t'36 policy_guards /\ final_guard_id _t'36 policy_guards=_t'55.
Proof. repeat split;reflexivity. Qed.
Lemma guard_append_source e m start first middle count g values bad :
 (forall k,store_path main_ge(fun after=>after=m)(State f_main start k e first m)count
  (State f_main Sskip k e middle m)) ->
 guard_valid g -> policy_image m values -> e!_policy__1=None ->
 middle!(guard_input g)=Some(Val.of_bool bad) ->
 forall k,store_path main_ge(fun after=>after=m)
 (State f_main(Ssequence start(guard_statement g))k e first m)
 (count+2+(if bad then 2 else 5))
 (State f_main Sskip k e(guard_env g middle bad(nth(Z.to_nat(guard_index g))values 0))m).
Proof.
 intros PREFIX VALID IMAGE GLOBAL REG k.
 replace(count+2+(if bad then 2 else 5))%nat with(S(count+S(if bad then 2 else 5)))%nat by lia.
 bounds_route;eapply store_path_trans;[apply PREFIX|].
 bounds_route;apply guard_source;assumption.
Qed.
Theorem guard_sequence_source e m guards values : Forall guard_valid guards ->
 policy_image m values -> e!_policy__1=None ->
 forall start first middle initial_count id bad,
 guard_links id guards -> middle!id=Some(Val.of_bool bad) ->
 (forall k,store_path main_ge(fun after=>after=m)(State f_main start k e first m)initial_count
  (State f_main Sskip k e middle m)) ->
 exists count final,(count<=initial_count+7*length guards)%nat /\
 (forall k,store_path main_ge(fun after=>after=m)
  (State f_main(guard_sequence start guards)k e first m)count(State f_main Sskip k e final m)) /\
 final!(final_guard_id id guards)=Some(Val.of_bool(bad||guard_results values guards)).
Proof.
 intros VALID IMAGE GLOBAL;induction VALID as[|g rest VALID REST IH];
 intros start first middle initial_count id bad LINKS REG PREFIX.
 - exists initial_count,middle;split;[cbn;lia|]. split;[exact PREFIX|].
   cbn[final_guard_id guard_results existsb];rewrite orb_false_r;exact REG.
 - destruct LINKS as[LINK LINKS].
   pose proof(guard_append_source e m start first middle initial_count g values bad PREFIX VALID IMAGE GLOBAL
    ltac:(rewrite LINK;exact REG))as NEXT.
   destruct(IH(Ssequence start(guard_statement g))first
     (guard_env g middle bad(nth(Z.to_nat(guard_index g))values 0))
     (initial_count+2+(if bad then 2 else 5))%nat(guard_output g)
     (bad||guard_bad g(nth(Z.to_nat(guard_index g))values 0))LINKS(guard_env_result _ _ _ _)NEXT)
   as[count[final[BOUND[PATH RESULT]]]].
   exists count,final;split;[cbn;destruct bad;cbn in BOUND;lia|].
   split;[exact PATH|]. cbn[final_guard_id guard_results existsb]in *.
   rewrite <-orb_assoc in RESULT;exact RESULT.
Qed.
Theorem bounds_conditions_source e le m argc bytes values :
 17<=argc<=2147483647 -> 0<=bytes<=Int64.max_unsigned ->
 le!_argc=Some(Vint(Int.repr argc)) -> le!_bytes=Some(Vlong(Int64.repr bytes)) ->
 e!_policy__1=None -> policy_image m values ->
 exists count final,(count<=135)%nat /\
 (forall k,store_path main_ge(fun after=>after=m)(State f_main bounds_conditions k e le m)count
  (State f_main Sskip k e final m)) /\
 final!_t'55=Some(Val.of_bool(bounds_rejected argc bytes values)).
Proof.
 intros COUNT BYTES ARGC TOTAL GLOBAL IMAGE.
 destruct(guard_sequence_source e m policy_guards values policy_guards_valid IMAGE GLOBAL
  bounds_start le(bounds_start_env le argc bytes)2 _t'36(initial_bad argc bytes)
  (proj1 policy_guard_links)ltac:(apply PTree.gss)
  (fun k=>bounds_start_source e le m k argc bytes COUNT BYTES ARGC TOTAL))as[n[final[BOUND[PATH RESULT]]]].
 exists n,final;split;[exact BOUND|]. split;[exact PATH|exact RESULT].
Qed.
