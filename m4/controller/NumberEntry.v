(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageController Require Import NumberSlice NumberStructure NumberMath NumberWords NumberMemory.
Import ListNotations.
Open Scope Z_scope.
Ltac number_next := eapply store_next; [cbn [memory_of]; eassumption| |].
Ltac number_route := number_next; [apply unchanged_store_edge;WriteAll.structural|].
Ltac number_set := number_next; [eapply certified_set_edge;number_expression|].
Ltac number_branch choice := number_next;
 [apply unchanged_store_edge; eapply edge_if with (b:=choice); [WriteAll.expression|]|].
Theorem number_empty_source ge m b ofs output k :
 number_input m b ofs [] ->
 store_path ge (fun after => after=m) (number_initial (Vptr b ofs) output k m) 7
 (Returnstate (Vint Int.mone) (call_cont k) m).
Proof.
 intros INPUT;assert (SAME : m=m) by reflexivity.
 destruct(number_read_head m b ofs [] Byte.zero [] INPUT eq_refl) as [UNSIGNED SIGNED].
 number_next;[apply number_entry|].
 unfold f_number;cbn [fn_body].
 number_route;number_route.
 number_set;[exact SIGNED|].
 number_route.
 number_next;[apply unchanged_store_edge;eapply edge_if with (b:=true);
 [WriteAll.expression|reflexivity]|].
 number_next;[apply unchanged_store_edge;eapply edge_return;[WriteAll.expression|reflexivity]|].
 apply store_done;exact SAME.
Qed.
