(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Actual loop reads, call, result branch and finite control paths. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberStructure NumberStorage NumberControl.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues.
Import ListNotations.
Open Scope Z_scope.
Definition numeric_loaded le x i := PTree.set _t'293(Vptr main_policy_block(Ptrofs.repr(8*i)))
 (PTree.set _t'292(input_pointer x)le).
Definition numeric_returned le parsed := PTree.set _t'9(number_code parsed)le.
Definition numeric_advanced le i := PTree.set _i(Vint(Int.repr(i+1)))(numeric_returned le(Some 0)).
Definition numeric_loop_cont k := Kloop1 numeric_body numeric_increment k.
Definition numeric_number_cont e le k := Kcall(Some _t'9)f_main e le(Kseq numeric_check(numeric_loop_cont k)).
Definition numeric_failure_state e le k m := State f_main numeric_report
 (Kseq numeric_report_suffix(Kseq numeric_failure_return(numeric_loop_cont k)))e le m.
Ltac main_next := eapply store_next;[cbn [memory_of];eassumption| |].
Ltac main_route := main_next;[apply unchanged_store_edge;WriteAll.structural|].
Lemma numeric_to_call e le m fields argv ofs i x k P :
 numeric_locals e fields -> numeric_registers le argv ofs i -> 0<=i<10 ->
 Mem.loadv Mptr m(Vptr argv(argument_offset ofs i))=Some(input_pointer x) ->
 Mem.loadv Mptr m(Vptr fields(Ptrofs.repr(8*i)))=Some(Vptr main_policy_block(Ptrofs.repr(8*i))) -> P m ->
 store_path main_ge P(State f_main numeric_loop k e le m)12
 (number_initial(input_pointer x)(Vptr main_policy_block(Ptrofs.repr(8*i)))
  (numeric_number_cont e(numeric_loaded le x i)k)m).
Proof.
 intros [LOCAL NUMBER] REGS INDEX ARG FIELD GOOD.
 assert (I : le ! _i=Some(Vint(Int.repr i))) by exact(proj2 REGS).
 rewrite(proj1 numeric_loop_structure);main_route.
 rewrite(proj1(proj2 numeric_loop_structure));main_route;main_unfold numeric_test.
 main_next;[eapply certified_if_edge with(v:=Val.of_bool(i<?10))(b:=true)|].
 - eapply binary_expression_value;[apply old_expression_value;apply value_temp;exact I|
     apply old_expression_value;apply value_int|apply main_index_test;lia].
 - rewrite number_bool_value;f_equal;apply Z.ltb_lt;lia.
 - main_route;main_route;main_unfold numeric_read;main_route.
   main_next;[eapply certified_set_edge;eapply main_pointer_load;
    [apply main_argument_pointer_value with(argv:=argv)(ofs:=ofs)(i:=i);[exact REGS|exact INDEX]|exact ARG]|].
   main_route;main_route.
   main_next;[eapply certified_set_edge;eapply main_pointer_load;
    [apply main_field_pointer_value;[exact LOCAL|WriteAll.lookup|exact INDEX]|exact FIELD]|].
   main_route.
   main_next;[eapply certified_call_edge|].
   + reflexivity.
   + apply old_expression_value;eapply value_function;[exact NUMBER|exact(proj1 main_number_binding)|reflexivity].
   + repeat first[apply no_argument_values|eapply cons_argument_values;
       [apply old_expression_value;WriteAll.expression|reflexivity|]].
   + exact(proj2 main_number_binding).
   + reflexivity.
   + apply store_done;exact GOOD.
Qed.
Lemma numeric_after_success e le m argv ofs i value k P :
 numeric_registers le argv ofs i -> 0<=i<10 -> P m ->
 store_path main_ge P(Returnstate(number_code(Some value))(numeric_number_cont e le k)m)6
 (State f_main numeric_loop k e(numeric_advanced le i)m).
Proof.
 intros [ARGV INDEX] BOUND GOOD.
 unfold numeric_number_cont,numeric_advanced,numeric_returned,numeric_loop_cont.
 main_route;main_route;main_unfold numeric_check.
 main_next;[apply unchanged_store_edge;eapply edge_if with(b:=false);[WriteAll.expression|reflexivity]|].
 main_route;main_unfold numeric_increment.
 main_next;[eapply certified_set_edge;eapply binary_expression_value;
  [apply old_expression_value;apply value_temp;WriteAll.lookup|
   apply old_expression_value;apply value_int|apply main_index_add;lia]|].
 main_route;apply store_done;exact GOOD.
Qed.
Lemma numeric_after_failure e le m k P : P m ->
 store_path main_ge P(Returnstate(number_code None)(numeric_number_cont e le k)m)5
 (numeric_failure_state e(numeric_returned le None)k m).
Proof.
 intros GOOD;unfold numeric_number_cont,numeric_returned,numeric_loop_cont,numeric_failure_state.
 main_route;main_route;main_unfold numeric_check.
 main_next;[apply unchanged_store_edge;eapply edge_if with(b:=true);[WriteAll.expression|reflexivity]|].
 main_route;main_route;apply store_done;exact GOOD.
Qed.
Lemma numeric_loop_finished e le m argv ofs k P : numeric_registers le argv ofs 10 -> P m ->
 store_path main_ge P(State f_main numeric_loop k e le m)5(State f_main Sskip k e le m).
Proof.
 intros [ARGV INDEX] GOOD;rewrite(proj1 numeric_loop_structure);main_route.
 rewrite(proj1(proj2 numeric_loop_structure));main_route;main_unfold numeric_test.
 main_next;[apply unchanged_store_edge;eapply edge_if with(b:=false);[WriteAll.expression|reflexivity]|].
 main_route;main_route;apply store_done;exact GOOD.
Qed.
Lemma numeric_loaded_registers le argv ofs i x : numeric_registers le argv ofs i ->
 numeric_registers(numeric_loaded le x i)argv ofs i.
Proof. intros [ARGV INDEX];unfold numeric_registers,numeric_loaded;split;WriteAll.lookup. Qed.
Lemma numeric_advanced_registers le argv ofs i : numeric_registers le argv ofs i ->
 numeric_registers(numeric_advanced le i)argv ofs(i+1).
Proof. intros [ARGV INDEX];unfold numeric_registers,numeric_advanced,numeric_returned;split;WriteAll.lookup. Qed.
Lemma numeric_returned_registers le argv ofs i parsed : numeric_registers le argv ofs i ->
 numeric_registers(numeric_returned le parsed)argv ofs i.
Proof. intros [ARGV INDEX];unfold numeric_registers,numeric_returned;split;WriteAll.lookup. Qed.
