(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Actual initialization and transition into subsequent bounds. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import ArgumentStructure ArgumentValues ArgumentControl ArgumentMemory.
Import ListNotations.
Open Scope Z_scope.
Definition argument_initial_env le := PTree.set _i__1(Vint(Int.repr 16))
 (PTree.set _bytes(Vlong(Int64.repr 0))le).
Lemma argument_initialize e le m k :
 store_path main_ge(fun after=>after=m)(State f_main argument_suffix k e le m)7
 (State f_main argument_loop(Kseq after_arguments k)e(argument_initial_env le)m).
Proof.
 unfold argument_initial_env;rewrite(proj1 argument_structure);argument_route.
 argument_unfold argument_bytes_init;argument_next.
 - apply certified_set_edge;eapply cast_expression_value;
   [apply old_expression_value;apply value_int|reflexivity].
 - argument_route;argument_route.
   change argument_loop_region with(Ssequence(Sset _i__1(Econst_int(Int.repr 16)tint))argument_loop).
   argument_route;argument_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
   argument_route;apply store_done;reflexivity.
Qed.
Lemma argument_initialize_registers le argv ofs argc :
 le!_argv=Some(Vptr argv ofs) -> le!_argc=Some(Vint(Int.repr argc)) ->
 argument_registers(argument_initial_env le)argv ofs argc 16 0.
Proof. intros ARGV ARGC;unfold argument_registers,argument_initial_env;repeat split;WriteAll.lookup. Qed.
Lemma argument_to_bounds e le m k :
 store_path main_ge(fun after=>after=m)(State f_main Sskip(Kseq after_arguments k)e le m)1
 (State f_main after_arguments k e le m).
Proof. argument_route;apply store_done;reflexivity. Qed.
