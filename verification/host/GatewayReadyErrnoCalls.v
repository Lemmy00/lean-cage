(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual poll result reaches errno capture before restoration. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayReadySource GatewayReadyPhases GatewayReadyPollCalls
  GatewayCallPath GatewayRuntimeABI.
Import ListNotations.

Definition ready_polled_values (temporaries : temp_env) (status : int) :=
  PTree.set _result (Vint status) (PTree.set _t'5 (Vint status) temporaries).
Definition ready_errno_cont item temporaries := Kcall (Some _t'6) f_host_ready (ready_environment item) temporaries
  (Kseq ready_errno_bind (Kseq ready_after_errno ready_iteration_cont)).

Lemma actual_ready_errno_call (ge : Clight.genv) item temporaries memory symbol :
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  store_edge ge
    (State f_host_ready ready_errno_call (Kseq ready_errno_bind (Kseq ready_after_errno ready_iteration_cont))
      (ready_environment item) temporaries memory)
    (Callstate gateway_errno_location_definition [] (ready_errno_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac ready_retain target :=
  eapply gateway_retained_next with (next := target); [cbn; tauto | intro another |].

Lemma actual_ready_polled_errno_path (ge : Clight.genv) item temporaries status memory symbol :
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  gateway_retained_call_path ge gateway_errno_location_definition []
    (ready_errno_cont item (ready_polled_values temporaries status))
    (Returnstate (Vint status) (ready_poll_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION.
  ready_retain (State f_host_ready Sskip (Kseq ready_poll_bind (Kseq ready_after_poll ready_iteration_cont))
    (ready_environment item) (PTree.set _t'5 (Vint status) temporaries) memory).
  { apply unchanged_store_edge, edge_returnstate. }
  ready_retain (State f_host_ready ready_poll_bind (Kseq ready_after_poll ready_iteration_cont)
    (ready_environment item) (PTree.set _t'5 (Vint status) temporaries) memory).
  { apply unchanged_store_edge, edge_skip_seq. }
  ready_retain (State f_host_ready Sskip (Kseq ready_after_poll ready_iteration_cont)
    (ready_environment item) (ready_polled_values temporaries status) memory).
  { apply certified_set_edge, old_expression_value, value_temp; apply PTree.gss. }
  ready_retain (State f_host_ready ready_after_poll ready_iteration_cont
    (ready_environment item) (ready_polled_values temporaries status) memory).
  { apply unchanged_store_edge, edge_skip_seq. }
  ready_retain (State f_host_ready ready_errno_sequence (Kseq ready_after_errno ready_iteration_cont)
    (ready_environment item) (ready_polled_values temporaries status) memory).
  { apply unchanged_store_edge, edge_seq. }
  ready_retain (State f_host_ready ready_errno_call (Kseq ready_errno_bind (Kseq ready_after_errno ready_iteration_cont))
    (ready_environment item) (ready_polled_values temporaries status) memory).
  { apply unchanged_store_edge, edge_seq. }
  ready_retain (Callstate gateway_errno_location_definition []
    (ready_errno_cont item (ready_polled_values temporaries status)) memory).
  { apply actual_ready_errno_call with (symbol := symbol); assumption. }
  constructor.
Qed.
