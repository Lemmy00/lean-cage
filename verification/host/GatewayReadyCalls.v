(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The real readiness loop invokes the proved control and clock helpers. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps ClightSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadySource GatewayReadyTests GatewayCallPath
  GatewayControlPaths.
Import ListNotations.

Definition ready_control_cont item temporaries := Kcall (Some _t'1) f_host_ready (ready_environment item) temporaries
  (Kseq ready_control_test (Kseq ready_after_control ready_iteration_cont)).
Definition ready_clock_cont item temporaries := Kcall (Some _t'2) f_host_ready (ready_environment item) temporaries
  (Kseq ready_clock_bind (Kseq ready_after_clock ready_iteration_cont)).

Lemma actual_ready_control_call (ge : Clight.genv) item temporaries stream_block stream_offset memory symbol :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  Genv.find_symbol ge _host_control = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (Internal f_host_control) ->
  store_edge ge
    (State f_host_ready ready_control_call (Kseq ready_control_test (Kseq ready_after_control ready_iteration_cont))
      (ready_environment item) temporaries memory)
    (Callstate (Internal f_host_control) [Vptr stream_block stream_offset] (ready_control_cont item temporaries) memory).
Proof.
  intros STREAM SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - eapply cons_argument_values with (v := Vptr stream_block stream_offset).
    + apply old_expression_value, value_temp; exact STREAM.
    + reflexivity.
    + apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Definition ready_clock_values (temporaries : temp_env) (returned : val) :=
  PTree.set _now returned (PTree.set _t'2 returned temporaries).
Definition ready_clock_guard_cont := Kseq ready_clock_test (Kseq ready_after_clock_guard ready_iteration_cont).

Lemma actual_ready_clock_guard_prefix (ge : Clight.genv) item temporaries returned memory :
  gateway_retained_prefix ge
    (State f_host_ready ready_clock_boolean ready_clock_guard_cont (ready_environment item)
      (ready_clock_values temporaries returned) memory)
    (Returnstate returned (ready_clock_cont item temporaries) memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_ready Sskip
    (Kseq ready_clock_bind (Kseq ready_after_clock ready_iteration_cont)) (ready_environment item)
    (PTree.set _t'2 returned temporaries) memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_prefix_next with (next := State f_host_ready ready_clock_bind
    (Kseq ready_after_clock ready_iteration_cont) (ready_environment item)
    (PTree.set _t'2 returned temporaries) memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_prefix_next with (next := State f_host_ready Sskip
    (Kseq ready_after_clock ready_iteration_cont) (ready_environment item)
    (ready_clock_values temporaries returned) memory).
  - cbn; tauto.
  - intro another; apply certified_set_edge, old_expression_value, value_temp; apply PTree.gss.
  - eapply gateway_prefix_next with (next := State f_host_ready ready_after_clock ready_iteration_cont
      (ready_environment item) (ready_clock_values temporaries returned) memory);
      [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_prefix_next with (next := State f_host_ready ready_clock_guard
      (Kseq ready_after_clock_guard ready_iteration_cont) (ready_environment item)
      (ready_clock_values temporaries returned) memory);
      [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
    eapply gateway_prefix_next with (next := State f_host_ready ready_clock_boolean ready_clock_guard_cont
      (ready_environment item) (ready_clock_values temporaries returned) memory);
      [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
    exact (gateway_prefix_reached ge
      (State f_host_ready ready_clock_boolean ready_clock_guard_cont (ready_environment item)
        (ready_clock_values temporaries returned) memory) memory).
Qed.


Lemma actual_ready_loop_control_path (ge : Clight.genv) item temporaries stream_block stream_offset memory symbol :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  Genv.find_symbol ge _host_control = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (Internal f_host_control) ->
  gateway_retained_call_path ge (Internal f_host_control) [Vptr stream_block stream_offset] (ready_control_cont item temporaries)
    (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item) temporaries memory).
Proof.
  intros STREAM SYMBOL FUNCTION.
  eapply gateway_retained_next with (next := State f_host_ready ready_iteration_body ready_iteration_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_loop |].
  eapply gateway_retained_next with (next := State f_host_ready Sskip (Kseq ready_iteration ready_iteration_cont)
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  eapply gateway_retained_next with (next := State f_host_ready ready_iteration ready_iteration_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_retained_next with (next := State f_host_ready ready_control_sequence
    (Kseq ready_after_control ready_iteration_cont) (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  eapply gateway_retained_next with (next := State f_host_ready ready_control_call
    (Kseq ready_control_test (Kseq ready_after_control ready_iteration_cont)) (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  eapply gateway_retained_next with (next := Callstate (Internal f_host_control) [Vptr stream_block stream_offset]
    (ready_control_cont item temporaries) memory);
    [cbn; tauto | intro another; eapply actual_ready_control_call; eassumption | constructor].
Qed.

Lemma actual_ready_clock_call (ge : Clight.genv) item temporaries memory symbol :
  Genv.find_symbol ge _host_now = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (Internal f_host_now) ->
  store_edge ge
    (State f_host_ready ready_clock_call (Kseq ready_clock_bind (Kseq ready_after_clock ready_iteration_cont))
      (ready_environment item) temporaries memory)
    (Callstate (Internal f_host_now) [] (ready_clock_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_ready_after_zero_control_path (ge : Clight.genv) item temporaries memory symbol :
  temporaries ! _t'1 = Some (Vint Int.zero) ->
  Genv.find_symbol ge _host_now = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (Internal f_host_now) ->
  gateway_retained_call_path ge (Internal f_host_now) [] (ready_clock_cont item temporaries)
    (State f_host_ready ready_control_test (Kseq ready_after_control ready_iteration_cont)
      (ready_environment item) temporaries memory).
Proof.
  intros ZERO SYMBOL FUNCTION.
  eapply gateway_retained_next with (next := State f_host_ready Sskip
    (Kseq ready_after_control ready_iteration_cont) (ready_environment item) temporaries memory).
  - cbn; tauto.
  - intro another; apply certified_if_edge with (v := Vint Int.zero) (b := false);
      [apply old_expression_value, value_temp; exact ZERO | reflexivity].
  - eapply gateway_retained_next with (next := State f_host_ready ready_after_control ready_iteration_cont
      (ready_environment item) temporaries memory);
      [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_retained_next with (next := State f_host_ready ready_clock_sequence
      (Kseq ready_after_clock ready_iteration_cont) (ready_environment item) temporaries memory);
      [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
    eapply gateway_retained_next with (next := State f_host_ready ready_clock_call
      (Kseq ready_clock_bind (Kseq ready_after_clock ready_iteration_cont)) (ready_environment item) temporaries memory);
      [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
    eapply gateway_retained_next with (next := Callstate (Internal f_host_now) [] (ready_clock_cont item temporaries) memory);
      [cbn; tauto | intro another; eapply actual_ready_clock_call; eassumption | constructor].
Qed.

Lemma actual_ready_zero_control_clock_path (ge : Clight.genv) item temporaries memory symbol :
  Genv.find_symbol ge _host_now = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (Internal f_host_now) ->
  gateway_retained_call_path ge (Internal f_host_now) []
    (ready_clock_cont item (PTree.set _t'1 (Vint Int.zero) temporaries))
    (Returnstate (Vint Int.zero) (ready_control_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION.
  eapply gateway_retained_next with (next := State f_host_ready Sskip
    (Kseq ready_control_test (Kseq ready_after_control ready_iteration_cont))
    (ready_environment item) (PTree.set _t'1 (Vint Int.zero) temporaries) memory).
  - cbn; tauto.
  - intro another; apply unchanged_store_edge, edge_returnstate.
  - eapply gateway_retained_next with (next := State f_host_ready ready_control_test
      (Kseq ready_after_control ready_iteration_cont) (ready_environment item)
      (PTree.set _t'1 (Vint Int.zero) temporaries) memory).
    + cbn; tauto.
    + intro another; apply unchanged_store_edge, edge_skip_seq.
    + apply actual_ready_after_zero_control_path with (symbol := symbol);
        [apply PTree.gss | exact SYMBOL | exact FUNCTION].
Qed.
