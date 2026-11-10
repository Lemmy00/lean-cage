(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual poll stores precede the actual SaveThread call. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine StoreSteps ClightSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayReadySource GatewayReadyPhases GatewayReadyTimeout
  GatewayControlPaths GatewayCallPath GatewayRuntimeABI.
Import ListNotations.

Definition ready_descriptor_cont := Kseq ready_after_descriptor ready_iteration_cont.
Definition ready_events_cont := Kseq ready_after_events ready_iteration_cont.
Definition ready_revents_cont := Kseq ready_after_revents ready_iteration_cont.
Definition ready_save_cont item temporaries := Kcall (Some _t'4) f_host_ready (ready_environment item) temporaries
  (Kseq ready_save_bind (Kseq ready_after_save ready_iteration_cont)).

Lemma actual_ready_descriptor_prefix ge item temporaries memory :
  gateway_retained_prefix ge
    (State f_host_ready ready_descriptor_load (Kseq ready_descriptor_store ready_descriptor_cont)
      (ready_environment item) temporaries memory)
    (State f_host_ready Sskip ready_after_timeout_cont (ready_environment item) temporaries memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_ready ready_after_clock_guard ready_iteration_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_prefix_next with (next := State f_host_ready ready_descriptor_sequence ready_descriptor_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  eapply gateway_prefix_next with (next := State f_host_ready ready_descriptor_load
    (Kseq ready_descriptor_store ready_descriptor_cont) (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  exact (gateway_prefix_reached ge _ memory).
Qed.

Lemma actual_ready_events_prefix ge item temporaries memory :
  gateway_retained_prefix ge
    (State f_host_ready ready_events_store ready_events_cont (ready_environment item) temporaries memory)
    (State f_host_ready Sskip ready_descriptor_cont (ready_environment item) temporaries memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_ready ready_after_descriptor ready_iteration_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_prefix_next with (next := State f_host_ready ready_events_store ready_events_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  exact (gateway_prefix_reached ge _ memory).
Qed.

Lemma actual_ready_revents_prefix ge item temporaries memory :
  gateway_retained_prefix ge
    (State f_host_ready ready_revents_store ready_revents_cont (ready_environment item) temporaries memory)
    (State f_host_ready Sskip ready_events_cont (ready_environment item) temporaries memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_ready ready_after_events ready_iteration_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_prefix_next with (next := State f_host_ready ready_revents_store ready_revents_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  exact (gateway_prefix_reached ge _ memory).
Qed.

Lemma actual_ready_save_call (ge : Clight.genv) item temporaries memory symbol :
  Genv.find_symbol ge _PyEval_SaveThread = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_save_thread_definition ->
  store_edge ge
    (State f_host_ready ready_save_call (Kseq ready_save_bind (Kseq ready_after_save ready_iteration_cont))
      (ready_environment item) temporaries memory)
    (Callstate gateway_save_thread_definition [] (ready_save_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_ready_save_path (ge : Clight.genv) item temporaries memory symbol :
  Genv.find_symbol ge _PyEval_SaveThread = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_save_thread_definition ->
  gateway_retained_call_path ge gateway_save_thread_definition [] (ready_save_cont item temporaries)
    (State f_host_ready Sskip ready_revents_cont (ready_environment item) temporaries memory).
Proof.
  intros SYMBOL FUNCTION.
  eapply gateway_retained_next with (next := State f_host_ready ready_after_revents ready_iteration_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_retained_next with (next := State f_host_ready ready_save_sequence
    (Kseq ready_after_save ready_iteration_cont) (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  eapply gateway_retained_next with (next := State f_host_ready ready_save_call
    (Kseq ready_save_bind (Kseq ready_after_save ready_iteration_cont)) (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  eapply gateway_retained_next with (next := Callstate gateway_save_thread_definition []
    (ready_save_cont item temporaries) memory);
    [cbn; tauto | intro another; apply actual_ready_save_call with (symbol := symbol); assumption | constructor].
Qed.
