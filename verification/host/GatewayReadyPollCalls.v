(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The exact saved thread token accompanies the actual poll call. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayReadySource GatewayReadyPhases GatewayReadySetupPaths
  GatewayCallPath GatewayRuntimeABI GatewayPrefix.
Import ListNotations.

Definition ready_saved_values (temporaries : temp_env) (saved : val) :=
  PTree.set _saved saved (PTree.set _t'4 saved temporaries).
Definition ready_poll_cont item temporaries := Kcall (Some _t'5) f_host_ready (ready_environment item) temporaries
  (Kseq ready_poll_bind (Kseq ready_after_poll ready_iteration_cont)).

Lemma actual_ready_poll_call (ge : Clight.genv) item temporaries memory symbol :
  Genv.find_symbol ge _poll = Some symbol -> Genv.find_funct_ptr ge symbol = Some gateway_poll_definition ->
  store_edge ge
    (State f_host_ready ready_poll_call (Kseq ready_poll_bind (Kseq ready_after_poll ready_iteration_cont))
      (ready_environment item) temporaries memory)
    (Callstate gateway_poll_definition [Vptr item Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 100)]
      (ready_poll_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - eapply cons_argument_values with (v := Vptr item Ptrofs.zero).
    + apply local_address_expression; apply PTree.gss.
    + reflexivity.
    + eapply cons_argument_values with (v := Vint Int.one).
      * apply old_expression_value; constructor.
      * reflexivity.
      * eapply cons_argument_values with (v := Vint (Int.repr 100));
          [apply old_expression_value; constructor | reflexivity | apply no_argument_values].
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac ready_retain target :=
  eapply gateway_retained_next with (next := target); [cbn; tauto | intro another |].

Lemma actual_ready_saved_poll_path (ge : Clight.genv) item temporaries saved memory symbol :
  Genv.find_symbol ge _poll = Some symbol -> Genv.find_funct_ptr ge symbol = Some gateway_poll_definition ->
  gateway_retained_call_path ge gateway_poll_definition
    [Vptr item Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 100)]
    (ready_poll_cont item (ready_saved_values temporaries saved))
    (Returnstate saved (ready_save_cont item temporaries) memory).
Proof.
  intros SYMBOL FUNCTION.
  ready_retain (State f_host_ready Sskip (Kseq ready_save_bind (Kseq ready_after_save ready_iteration_cont))
    (ready_environment item) (PTree.set _t'4 saved temporaries) memory).
  { apply unchanged_store_edge, edge_returnstate. }
  ready_retain (State f_host_ready ready_save_bind (Kseq ready_after_save ready_iteration_cont)
    (ready_environment item) (PTree.set _t'4 saved temporaries) memory).
  { apply unchanged_store_edge, edge_skip_seq. }
  ready_retain (State f_host_ready Sskip (Kseq ready_after_save ready_iteration_cont)
    (ready_environment item) (ready_saved_values temporaries saved) memory).
  { apply certified_set_edge, old_expression_value, value_temp; apply PTree.gss. }
  ready_retain (State f_host_ready ready_after_save ready_iteration_cont
    (ready_environment item) (ready_saved_values temporaries saved) memory).
  { apply unchanged_store_edge, edge_skip_seq. }
  ready_retain (State f_host_ready ready_poll_sequence (Kseq ready_after_poll ready_iteration_cont)
    (ready_environment item) (ready_saved_values temporaries saved) memory).
  { apply unchanged_store_edge, edge_seq. }
  ready_retain (State f_host_ready ready_poll_call (Kseq ready_poll_bind (Kseq ready_after_poll ready_iteration_cont))
    (ready_environment item) (ready_saved_values temporaries saved) memory).
  { apply unchanged_store_edge, edge_seq. }
  ready_retain (Callstate gateway_poll_definition [Vptr item Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 100)]
    (ready_poll_cont item (ready_saved_values temporaries saved)) memory).
  { apply actual_ready_poll_call with (symbol := symbol); assumption. }
  constructor.
Qed.
