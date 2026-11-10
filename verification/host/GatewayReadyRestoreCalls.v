(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Restore uses the exact saved token before actual signal dispatch. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayReadySource GatewayReadyPhases GatewayReadyCapture
  GatewayControlPaths GatewayCallPath GatewayRuntimeABI.
Import ListNotations.

Definition ready_restore_cont item temporaries := Kcall None f_host_ready (ready_environment item) temporaries
  (Kseq ready_after_restore ready_iteration_cont).
Definition ready_signals_cont item temporaries := Kcall (Some _t'7) f_host_ready (ready_environment item) temporaries
  (Kseq ready_signals_test (Kseq ready_after_signals ready_iteration_cont)).

Lemma actual_ready_restore_call (ge : Clight.genv) item temporaries saved memory symbol :
  (exists object offset, saved = Vptr object offset) -> temporaries ! _saved = Some saved ->
  Genv.find_symbol ge _PyEval_RestoreThread = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_restore_thread_definition ->
  store_edge ge
    (State f_host_ready ready_restore_call (Kseq ready_after_restore ready_iteration_cont)
      (ready_environment item) temporaries memory)
    (Callstate gateway_restore_thread_definition [saved] (ready_restore_cont item temporaries) memory).
Proof.
  intros (object & offset & SAME) SAVED SYMBOL FUNCTION; subst saved.
  eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - eapply cons_argument_values with (v := Vptr object offset);
      [apply old_expression_value, value_temp; exact SAVED | reflexivity | apply no_argument_values].
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac ready_retain target :=
  eapply gateway_retained_next with (next := target); [cbn; tauto | intro another |].

Lemma actual_ready_captured_restore_path (ge : Clight.genv) item temporaries saved memory symbol :
  (exists object offset, saved = Vptr object offset) -> temporaries ! _saved = Some saved ->
  Genv.find_symbol ge _PyEval_RestoreThread = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_restore_thread_definition ->
  gateway_retained_call_path ge gateway_restore_thread_definition [saved] (ready_restore_cont item temporaries)
    (State f_host_ready Sskip (Kseq ready_after_errno ready_iteration_cont) (ready_environment item) temporaries memory).
Proof.
  intros POINTER SAVED SYMBOL FUNCTION.
  ready_retain (State f_host_ready ready_after_errno ready_iteration_cont (ready_environment item) temporaries memory).
  { apply unchanged_store_edge, edge_skip_seq. }
  ready_retain (State f_host_ready ready_restore_call (Kseq ready_after_restore ready_iteration_cont)
    (ready_environment item) temporaries memory).
  { apply unchanged_store_edge, edge_seq. }
  ready_retain (Callstate gateway_restore_thread_definition [saved] (ready_restore_cont item temporaries) memory).
  { apply actual_ready_restore_call with (symbol := symbol); assumption. }
  constructor.
Qed.

Lemma actual_ready_signals_call (ge : Clight.genv) item temporaries memory symbol :
  Genv.find_symbol ge _PyErr_CheckSignals = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_check_signals_definition ->
  store_edge ge
    (State f_host_ready ready_signals_call (Kseq ready_signals_test (Kseq ready_after_signals ready_iteration_cont))
      (ready_environment item) temporaries memory)
    (Callstate gateway_check_signals_definition [] (ready_signals_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_ready_restored_signals_path (ge : Clight.genv) item temporaries ignored memory symbol :
  Genv.find_symbol ge _PyErr_CheckSignals = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_check_signals_definition ->
  gateway_retained_call_path ge gateway_check_signals_definition [] (ready_signals_cont item temporaries)
    (Returnstate ignored (ready_restore_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION.
  ready_retain (State f_host_ready Sskip (Kseq ready_after_restore ready_iteration_cont)
    (ready_environment item) temporaries memory).
  { apply unchanged_store_edge, edge_returnstate. }
  ready_retain (State f_host_ready ready_after_restore ready_iteration_cont (ready_environment item) temporaries memory).
  { apply unchanged_store_edge, edge_skip_seq. }
  ready_retain (State f_host_ready ready_signals_sequence (Kseq ready_after_signals ready_iteration_cont)
    (ready_environment item) temporaries memory).
  { apply unchanged_store_edge, edge_seq. }
  ready_retain (State f_host_ready ready_signals_call
    (Kseq ready_signals_test (Kseq ready_after_signals ready_iteration_cont)) (ready_environment item) temporaries memory).
  { apply unchanged_store_edge, edge_seq. }
  ready_retain (Callstate gateway_check_signals_definition [] (ready_signals_cont item temporaries) memory).
  { apply actual_ready_signals_call with (symbol := symbol); assumption. }
  constructor.
Qed.

Lemma actual_ready_zero_signals_prefix ge item temporaries memory :
  gateway_retained_prefix ge
    (State f_host_ready ready_after_signals ready_iteration_cont (ready_environment item)
      (PTree.set _t'7 (Vint Int.zero) temporaries) memory)
    (Returnstate (Vint Int.zero) (ready_signals_cont item temporaries) memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_ready Sskip
    (Kseq ready_signals_test (Kseq ready_after_signals ready_iteration_cont))
    (ready_environment item) (PTree.set _t'7 (Vint Int.zero) temporaries) memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_prefix_next with (next := State f_host_ready ready_signals_test
    (Kseq ready_after_signals ready_iteration_cont) (ready_environment item)
    (PTree.set _t'7 (Vint Int.zero) temporaries) memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_prefix_next with (next := State f_host_ready Sskip
    (Kseq ready_after_signals ready_iteration_cont) (ready_environment item)
    (PTree.set _t'7 (Vint Int.zero) temporaries) memory).
  - cbn; tauto.
  - intro another; apply certified_if_edge with (v := Vint Int.zero) (b := false);
      [apply old_expression_value, value_temp; apply PTree.gss | reflexivity].
  - eapply gateway_prefix_next with (next := State f_host_ready ready_after_signals ready_iteration_cont
      (ready_environment item) (PTree.set _t'7 (Vint Int.zero) temporaries) memory);
      [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
    exact (gateway_prefix_reached ge _ memory).
Qed.
