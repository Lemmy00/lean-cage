(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Real short-circuit source paths and unchanged memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsStructure BoundsWords BoundsMemory BoundsValues.
Import ListNotations.
Open Scope Z_scope.
Ltac bounds_next := eapply store_next;[reflexivity| |].
Ltac bounds_route := bounds_next;[apply unchanged_store_edge;WriteAll.structural|].
Definition guard_env g le (bad:bool) x := if bad then PTree.set(guard_output g)(Vint Int.one)le
 else PTree.set(guard_output g)(Val.of_bool(guard_bad g x))
  (PTree.set(guard_read g)(Vlong(Int64.repr x))le).
Lemma guard_env_result g le bad x :
 (guard_env g le bad x)!(guard_output g)=Some(Val.of_bool(bad||guard_bad g x)).
Proof. destruct bad;unfold guard_env;cbn[orb];rewrite PTree.gss;reflexivity. Qed.
Theorem guard_skipped g e le m k : le!(guard_input g)=Some(Val.of_bool true) ->
 store_path main_ge(fun after=>after=m)(State f_main(guard_statement g)k e le m)2
 (State f_main Sskip k e(PTree.set(guard_output g)(Vint Int.one)le)m).
Proof.
 intros REG;unfold guard_statement.
 bounds_next;[eapply certified_if_edge with(v:=Val.of_bool true)(b:=true);
 [apply old_expression_value;apply value_temp;exact REG|reflexivity]|].
 bounds_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
 apply store_done;reflexivity.
Qed.
Theorem guard_source g values e le m k bad : guard_valid g -> policy_image m values ->
 e!_policy__1=None -> le!(guard_input g)=Some(Val.of_bool bad) ->
 store_path main_ge(fun after=>after=m)(State f_main(guard_statement g)k e le m)
 (if bad then 2%nat else 5%nat)
 (State f_main Sskip k e(guard_env g le bad(nth(Z.to_nat(guard_index g))values 0))m).
Proof.
 intros VALID IMAGE GLOBAL REG;destruct bad;[apply guard_skipped;exact REG|].
 unfold guard_statement,guard_env;bounds_next.
 - eapply certified_if_edge with(v:=Val.of_bool false)(b:=false);
   [apply old_expression_value;apply value_temp;exact REG|reflexivity].
 - bounds_route;bounds_next.
   + apply certified_set_edge;apply policy_image_read;[exact IMAGE|exact GLOBAL|exact(proj1 VALID)].
   + bounds_route;bounds_next.
     * apply certified_set_edge;apply guard_expression_value;[exact VALID|
       eapply policy_image_range;[exact IMAGE|exact(proj1 VALID)]|apply PTree.gss].
     * apply store_done;reflexivity.
Qed.
Definition initial_bad argc bytes := (64<?argc-16)||(16384<?bytes).
Definition bounds_start_env le argc bytes := PTree.set _t'36(Val.of_bool(initial_bad argc bytes))le.
Theorem bounds_start_source e le m k argc bytes : 17<=argc<=2147483647 ->
 0<=bytes<=Int64.max_unsigned ->
 le!_argc=Some(Vint(Int.repr argc)) -> le!_bytes=Some(Vlong(Int64.repr bytes)) ->
 store_path main_ge(fun after=>after=m)(State f_main bounds_start k e le m)2
 (State f_main Sskip k e(bounds_start_env le argc bytes)m).
Proof.
 intros COUNT BYTES ARGC TOTAL;rewrite bounds_start_structure.
 unfold bounds_start_env,initial_bad;destruct(64<?argc-16)eqn:BAD;cbn[orb].
 - bounds_next.
   + eapply certified_if_edge with(v:=Val.of_bool(64<?argc-16))(b:=true).
     * apply bounds_count_value;assumption.
     * rewrite number_bool_value,BAD;reflexivity.
   + bounds_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
     apply store_done;reflexivity.
 - bounds_next.
   + eapply certified_if_edge with(v:=Val.of_bool(64<?argc-16))(b:=false).
     * apply bounds_count_value;assumption.
     * rewrite number_bool_value,BAD;reflexivity.
   + bounds_next;[apply certified_set_edge;apply bounds_bytes_value;[exact BYTES|exact TOTAL]|].
     apply store_done;reflexivity.
Qed.
