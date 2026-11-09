(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Every failed guard returns immediately; only the checked tail returns zero. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource.
From EntryProcess Require Import ProcessAllocation ProcessStructure ProcessPaths.
Import ListNotations.
Open Scope Z_scope.

Ltac admission_route := eapply store_next; [exact I|apply unchanged_store_edge; WriteAll.structural|].
Ltac admission_set := eapply store_next; [exact I|apply certified_set_edge|].

Theorem admission_guard_source e le memory k test tail bad :
  typeof test = tint ->
  expression_value admission_ge e le memory test (Val.of_bool bad) ->
  store_path admission_ge (fun _ => True)
    (State f_admit_child (Ssequence (Sifthenelse test admission_failure Sskip) tail) k e le memory)
    (if bad then 2 else 3)%nat
    (if bad then State f_admit_child admission_failure (Kseq tail k) e le memory
      else State f_admit_child tail k e le memory).
Proof.
  intros TYPE TEST; destruct bad; cbn; admission_route;
    eapply store_next; [exact I|apply certified_if_edge with (v:=Val.of_bool true) (b:=true)|
      |exact I|apply certified_if_edge with (v:=Val.of_bool false) (b:=false)|].
  - exact TEST.
  - rewrite TYPE; reflexivity.
  - apply store_done; exact I.
  - exact TEST.
  - rewrite TYPE; reflexivity.
  - admission_route; apply store_done; exact I.
Qed.

Theorem admission_finish_path e le before after k :
  Mem.free_list before (blocks_of_env admission_ge e) = Some after ->
  store_path admission_ge (fun _ => True)
    (State f_admit_child admission_return k e le before) 1
    (Returnstate (Vint Int.zero) (call_cont k) after).
Proof.
  intro FREE; rewrite admission_finish_source.
  eapply store_next; [exact I|eapply certified_local_return_edge|apply store_done; exact I].
  - apply old_expression_value,value_int.
  - reflexivity.
  - exact FREE.
Qed.

Theorem admission_failure_path e le before after k :
  Mem.free_list before (blocks_of_env admission_ge e) = Some after ->
  store_path admission_ge (fun _ => True)
    (State f_admit_child admission_failure k e le before) 1
    (Returnstate (Vint Int.mone) (call_cont k) after).
Proof.
  intro FREE; unfold admission_failure.
  eapply store_next; [exact I|eapply certified_local_return_edge|apply store_done; exact I].
  - apply old_expression_value; WriteAll.expression.
  - reflexivity.
  - exact FREE.
Qed.

Theorem admission_finish_process cell e le before after k :
  Mem.free_list before (blocks_of_env admission_ge e) = Some after ->
  ProcessMachine.process_steps admission_ge cell
    (live (State f_admit_child admission_return k e le before))
    (repeat process_source_event 1)
    (live (Returnstate (Vint Int.zero) (call_cont k) after)).
Proof.
  intro FREE. eapply process_store_path_actual,admission_finish_path; eassumption.
Qed.
