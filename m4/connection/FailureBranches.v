(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: Exact drop, short-report and ignored-return source branches. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess CallPaths
  LibraryMachine FailureSourceDraft FailureMemoryDraft.
Import ListNotations.
Open Scope Z_scope.

Definition failure_drop_temps fd stage error := PTree.set _t'3 (Vint Int.zero) (failure_temps fd stage error).
Definition failure_short_cont local fd stage error k := Kcall (Some _t'1) f_fail_child
  (failure_env local) (failure_drop_temps fd stage error)
  (Kseq failure_size (Kseq failure_write (Kseq failure_exit k))).
Definition failure_short_state local fd stage error short k m :=
  Callstate (Internal f_fault) [Vptr short Ptrofs.zero]
    (failure_short_cont local fd stage error k) m.
Definition failure_count (short : bool) := if short then 3 else 8.
Definition failure_write_temps fd stage error short :=
  PTree.set _t'2 (Vint (Int.repr (failure_count short)))
    (PTree.set _t'1 (Val.of_bool short) (failure_drop_temps fd stage error)).

Theorem failure_report_symbols : exists fb wb,
  Genv.find_symbol failure_ge _fault = Some fb /\
  Genv.find_funct failure_ge (Vptr fb Ptrofs.zero) = Some (Internal f_fault) /\
  Genv.find_symbol failure_ge _write_all = Some wb /\
  Genv.find_funct failure_ge (Vptr wb Ptrofs.zero) = Some (Internal f_write_all).
Proof. eexists; eexists. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. Qed.

Ltac failure_pure_route := eapply store_next; [reflexivity|apply unchanged_store_edge; WriteAll.structural|].
Ltac failure_pure_branch choice := eapply store_next; [reflexivity| |];
  [eapply certified_if_edge with (b:=choice); [failure_expression|reflexivity]|].
Ltac failure_pure_call symbol function := eapply store_next; [reflexivity| |];
  [eapply certified_call_edge; [reflexivity|
    apply old_expression_value; eapply value_function;
    [unfold failure_env; cbn; reflexivity|exact symbol|reflexivity]|
    failure_arguments|exact function|reflexivity]|].

Theorem failure_drop_path : forall local fd stage error k m,
  store_path failure_ge (fun after => after=m)
    (Returnstate (Vint Int.one) (failure_drop_cont local fd stage error k) m) 5
    (Callstate exit_definition [Vint (Int.repr 125)]
      (failure_exit_cont local (PTree.set _t'3 (Vint Int.one) (failure_temps fd stage error)) k) m).
Proof.
  intros. destruct failure_exit_symbol as [eb [ES EF]].
  unfold failure_drop_cont, failure_exit_cont, failure_after_drop, failure_exit.
  failure_pure_route. failure_pure_route. failure_pure_branch false.
  failure_pure_route. failure_pure_call ES EF. apply store_done; reflexivity.
Qed.

Theorem failure_not_drop_path : forall local fd stage error short k m,
  Genv.find_symbol failure_ge ___stringlit_9 = Some short ->
  store_path failure_ge (fun after => after=m)
    (Returnstate (Vint Int.zero) (failure_drop_cont local fd stage error k) m) 6
    (failure_short_state local fd stage error short k m).
Proof.
  intros local fd stage error short k m SS.
  destruct failure_report_symbols as [fb [wb [FS [FF [WS WF]]]]].
  unfold failure_drop_cont, failure_after_drop.
  failure_pure_route. failure_pure_route. failure_pure_branch true.
  failure_pure_route. failure_pure_route. unfold failure_fault.
  eapply store_next; [reflexivity| |].
  - eapply certified_call_edge; [reflexivity|
      apply old_expression_value; eapply value_function;
      [unfold failure_env; cbn; reflexivity|exact FS|reflexivity]| |exact FF|reflexivity].
    eapply cons_argument_values.
    + apply old_expression_value; eapply value_function;
      [unfold failure_env; cbn; reflexivity|exact SS|reflexivity].
    + reflexivity.
    + apply no_argument_values.
  - apply store_done; reflexivity.
Qed.

Theorem failure_short_or_full_path : forall local cell fd stage error short k m,
  store_path failure_ge (fun after => after=m)
    (Returnstate (Val.of_bool short) (failure_short_cont local fd stage error k) m) 6
    (Callstate (Internal f_write_all)
      (request_args (failure_request cell fd local (failure_count short)))
      (failure_write_cont local (failure_write_temps fd stage error short) k) m).
Proof.
  intros local cell fd stage error short k m.
  destruct failure_report_symbols as [fb [wb [FS [FF [WS WF]]]]].
  destruct short; unfold failure_short_cont, failure_size, failure_write, failure_drop_temps,
    failure_temps, failure_count, failure_write_temps, failure_write_cont, request_args, failure_request;
    cbn [Val.of_bool].
  all: failure_pure_route; failure_pure_route;
    first [failure_pure_branch true|failure_pure_branch false].
  all: eapply store_next; [reflexivity|eapply certified_set_edge; failure_expression|].
  all: failure_pure_route; failure_pure_call WS WF; apply store_done; reflexivity.
Qed.
