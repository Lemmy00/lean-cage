(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Actual loop entry, strlen call and short-circuit paths. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll Library.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure MainValues.
From LeanCageArguments Require Import StringMachine ArgumentStructure ArgumentWords ArgumentValues.
Import ListNotations.
Open Scope Z_scope.
Ltac argument_next := eapply store_next;[reflexivity| |].
Ltac argument_route := argument_next;[apply unchanged_store_edge;WriteAll.structural|].
Definition argument_loop_cont k := Kloop1 argument_body argument_increment k.
Definition argument_n_store := Sset _n(Etempvar _t'32 tulong).
Definition argument_read_cont k := Kseq argument_n_store
 (Kseq(Ssequence argument_check argument_add)(argument_loop_cont k)).
Definition argument_call_cont e le k := Kcall(Some _t'32)f_main e le(argument_read_cont k).
Definition argument_loaded le p := PTree.set _t'274(address_value p)le.
Definition argument_returned le n := PTree.set _n(Vlong(Int64.repr n))
 (PTree.set _t'32(Vlong(Int64.repr n))le).
Definition argument_checked le n := PTree.set _t'34(Val.of_bool(argument_bad n))(argument_returned le n).
Definition argument_advanced le n i total := PTree.set _i__1(Vint(Int.repr(i+1)))
 (PTree.set _bytes(Vlong(Int64.repr(total+n+1)))(argument_checked le n)).
Definition argument_check_cont k := Kseq argument_reject(Kseq argument_add(argument_loop_cont k)).
Definition argument_failure_state e le k m := State f_main argument_report
 (Kseq argument_finish(Kseq argument_return(Kseq argument_add(argument_loop_cont k))))e le m.
Definition argument_strlen_block := match Genv.find_symbol main_ge _strlen with Some b=>b|None=>1%positive end.
Lemma argument_strlen_binding : Genv.find_symbol main_ge _strlen=Some argument_strlen_block /\
 Genv.find_funct main_ge(Vptr argument_strlen_block Ptrofs.zero)=Some strlen_definition.
Proof. split;reflexivity. Qed.
Lemma argument_to_call e le m argv ofs argc i total p k :
 e!_strlen=None -> argument_registers le argv ofs argc i total ->
 16<=i<argc -> argc<=2147483647 ->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr(8*i))))=Some(address_value p) ->
 store_path main_ge(fun after=>after=m)(State f_main argument_loop k e le m)10
 (Callstate strlen_definition[address_value p](argument_call_cont e(argument_loaded le p)k)m).
Proof.
 intros GLOBAL[ARGV[ARGC[INDEX TOTAL]]] RANGE HIGH LOAD.
 change argument_loop with(Sloop argument_body argument_increment);argument_route.
 change argument_body with(Ssequence argument_test(Ssequence argument_read(Ssequence argument_check argument_add)));argument_route.
 argument_unfold argument_test;argument_next.
 - eapply certified_if_edge with(v:=Val.of_bool(i<?argc))(b:=true).
   + apply argument_test_value;try assumption;lia.
   + rewrite number_bool_value;f_equal;apply Z.ltb_lt;lia.
 - argument_route;argument_route;argument_unfold argument_read;argument_route;argument_route.
   argument_next.
   + apply certified_set_edge;eapply main_pointer_load;
     [eapply argument_pointer_value;[exact ARGV|exact INDEX|lia]|exact LOAD].
   + argument_route;argument_next.
     * eapply certified_call_edge.
       -- reflexivity.
       -- apply old_expression_value;eapply value_function;
          [exact GLOBAL|exact(proj1 argument_strlen_binding)|reflexivity].
       -- repeat first[apply no_argument_values|eapply cons_argument_values;
          [apply old_expression_value;WriteAll.expression|reflexivity|]].
       -- exact(proj2 argument_strlen_binding).
       -- reflexivity.
     * apply store_done;reflexivity.
Qed.
Lemma argument_return_to_size e le m k n :
 store_path main_ge(fun after=>after=m)
 (Returnstate(Vlong(Int64.repr n))(argument_call_cont e le k)m)6
 (State f_main argument_size_check(argument_check_cont k)e(argument_returned le n)m).
Proof.
 unfold argument_call_cont,argument_read_cont,argument_returned,argument_n_store,argument_check_cont.
 argument_route;argument_route;argument_next.
 - apply certified_set_edge;apply old_expression_value;WriteAll.expression.
 - argument_route;argument_route;change argument_check with(Ssequence argument_size_check argument_reject).
   argument_route;apply store_done;reflexivity.
Qed.
Lemma argument_size_source e le m k n : le!_n=Some(Vlong(Int64.repr n)) ->
 0<=n<=Int64.max_unsigned ->
 store_path main_ge(fun after=>after=m)(State f_main argument_size_check k e le m)2
 (State f_main Sskip k e(PTree.set _t'34(Val.of_bool(argument_bad n))le)m).
Proof.
 intros REG RANGE;argument_unfold argument_size_check.
 unfold argument_bad;destruct(n=?0)eqn:EMPTY;cbn[orb].
 - argument_next.
   + eapply certified_if_edge with(v:=Val.of_bool(n=?0))(b:=true).
     * apply argument_empty_expression;assumption.
     * rewrite number_bool_value,EMPTY;reflexivity.
   + argument_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
     apply store_done;reflexivity.
 - argument_next.
   + eapply certified_if_edge with(v:=Val.of_bool(n=?0))(b:=false).
     * apply argument_empty_expression;assumption.
     * rewrite number_bool_value,EMPTY;reflexivity.
   + argument_next;[apply certified_set_edge;apply argument_size_expression;[exact REG|exact RANGE]|].
     apply store_done;reflexivity.
Qed.
Lemma argument_size_to_failure e le m k n : argument_bad n=true ->
 store_path main_ge(fun after=>after=m)
 (State f_main Sskip(argument_check_cont k)e(argument_checked le n)m)4
 (argument_failure_state e(argument_checked le n)k m).
Proof.
 intros BAD;unfold argument_check_cont,argument_failure_state;argument_route.
 change argument_reject with(Sifthenelse(Etempvar _t'34 tint)argument_failure Sskip).
 argument_next.
 - apply unchanged_store_edge;eapply edge_if with(b:=true).
   + unfold argument_checked;rewrite BAD;WriteAll.expression.
   + reflexivity.
 - change argument_failure with(Ssequence(Ssequence argument_report argument_finish)argument_return).
   argument_route;argument_route;apply store_done;reflexivity.
Qed.
Lemma argument_size_to_success e le m k n i total :
 le!_i__1=Some(Vint(Int.repr i)) -> le!_bytes=Some(Vlong(Int64.repr total)) ->
 16<=i<2147483647 -> 0<=total<=4097*(i-16) -> 1<=n<=4096 ->
 store_path main_ge(fun after=>after=m)
 (State f_main Sskip(argument_check_cont k)e(argument_checked le n)m)7
 (State f_main argument_loop k e(argument_advanced le n i total)m).
Proof.
 intros INDEX TOTAL I T N;pose proof(argument_accumulator_range i n total I T N)as[RANGE HIGH].
 assert(BAD:argument_bad n=false)by(apply argument_bad_false;lia).
 unfold argument_check_cont,argument_advanced;argument_route.
 change argument_reject with(Sifthenelse(Etempvar _t'34 tint)argument_failure Sskip).
 argument_next.
 - apply unchanged_store_edge;eapply edge_if with(b:=false).
   + unfold argument_checked;rewrite BAD;WriteAll.expression.
   + reflexivity.
 - argument_route;argument_unfold argument_add;argument_next.
   + apply certified_set_edge;apply argument_sum_expression.
     * unfold argument_checked,argument_returned;WriteAll.lookup.
     * unfold argument_checked,argument_returned;WriteAll.lookup.
     * lia.
     * exact N.
     * exact HIGH.
   + unfold argument_loop_cont;argument_route;argument_unfold argument_increment;argument_next.
     * apply certified_set_edge;eapply binary_expression_value.
       -- apply old_expression_value;apply value_temp;unfold argument_checked,argument_returned;WriteAll.lookup.
       -- apply old_expression_value;apply value_int.
       -- apply argument_index_add;lia.
     * argument_route;apply store_done;reflexivity.
Qed.
Lemma argument_after_failure e le m k n : 0<=n<=Int64.max_unsigned -> argument_bad n=true ->
 store_path main_ge(fun after=>after=m)
 (Returnstate(Vlong(Int64.repr n))(argument_call_cont e le k)m)12
 (argument_failure_state e(argument_checked le n)k m).
Proof.
 intros RANGE BAD;eapply store_path_trans with(n:=6%nat);[apply argument_return_to_size|].
 eapply store_path_trans with(n:=2%nat);[apply argument_size_source;
 [unfold argument_returned;apply PTree.gss|exact RANGE]|].
 apply argument_size_to_failure;exact BAD.
Qed.
Lemma argument_after_success e le m k n i total :
 le!_i__1=Some(Vint(Int.repr i)) -> le!_bytes=Some(Vlong(Int64.repr total)) ->
 16<=i<2147483647 -> 0<=total<=4097*(i-16) -> 1<=n<=4096 ->
 store_path main_ge(fun after=>after=m)
 (Returnstate(Vlong(Int64.repr n))(argument_call_cont e le k)m)15
 (State f_main argument_loop k e(argument_advanced le n i total)m).
Proof.
 intros INDEX TOTAL I T N;eapply store_path_trans with(n:=6%nat);[apply argument_return_to_size|].
 eapply store_path_trans with(n:=2%nat);[apply argument_size_source;
 [unfold argument_returned;apply PTree.gss|change(0<=n<=18446744073709551615);lia]|].
 apply argument_size_to_success;assumption.
Qed.
Lemma argument_loop_finished e le m k argc :
 le!_argc=Some(Vint(Int.repr argc)) -> le!_i__1=Some(Vint(Int.repr argc)) ->
 16<=argc<=2147483647 ->
 store_path main_ge(fun after=>after=m)(State f_main argument_loop k e le m)5
 (State f_main Sskip k e le m).
Proof.
 intros ARGC INDEX RANGE;change argument_loop with(Sloop argument_body argument_increment);argument_route.
 change argument_body with(Ssequence argument_test(Ssequence argument_read(Ssequence argument_check argument_add)));argument_route.
 argument_unfold argument_test;argument_next.
 - eapply certified_if_edge with(v:=Val.of_bool(argc<?argc))(b:=false).
   + apply argument_test_value;try assumption;lia.
   + rewrite number_bool_value,Z.ltb_irrefl;reflexivity.
 - argument_route;argument_route;apply store_done;reflexivity.
Qed.
Lemma argument_loaded_registers le argv ofs argc i total p : argument_registers le argv ofs argc i total ->
 argument_registers(argument_loaded le p)argv ofs argc i total.
Proof. intros[A[B[C D]]];unfold argument_registers,argument_loaded;repeat split;WriteAll.lookup. Qed.
Lemma argument_checked_registers le argv ofs argc i total n : argument_registers le argv ofs argc i total ->
 argument_registers(argument_checked le n)argv ofs argc i total.
Proof. intros[A[B[C D]]];unfold argument_registers,argument_checked,argument_returned;repeat split;WriteAll.lookup. Qed.
Lemma argument_advanced_registers le argv ofs argc i total n : argument_registers le argv ofs argc i total ->
 argument_registers(argument_advanced le n i total)argv ofs argc(i+1)(total+n+1).
Proof. intros[A[B[C D]]];unfold argument_registers,argument_advanced,argument_checked,argument_returned;repeat split;WriteAll.lookup. Qed.
