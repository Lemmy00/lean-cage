(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Readiness consumes actual source layouts and actual callable bindings. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayReadySource GatewayClock GatewayBindings GatewayStreamLayout
  GatewayPollLayout GatewayRuntimeABI.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_ready_functions : list (ident * Ctypes.fundef Clight.function) :=
  [(_host_control, Internal f_host_control); (_host_now, Internal f_host_now);
   (_send, gateway_send_definition); (___errno_location, gateway_errno_location_definition);
   (_PyEval_SaveThread, gateway_save_thread_definition); (_poll, gateway_poll_definition);
   (_PyEval_RestoreThread, gateway_restore_thread_definition); (_PyErr_CheckSignals, gateway_check_signals_definition);
   (_clock_gettime, gateway_clock_gettime_definition)].

Definition gateway_ready_bindings (ge : Clight.genv) : Prop :=
  sizeof (genv_cenv ge) ready_item_type = 8 /\ sizeof (genv_cenv ge) clock_sample_type = 16 /\
  stream_member_layout ge _control 4 /\ stream_member_layout ge _cancellation_sent 8 /\
  poll_member_layout ge _fd 0 /\ poll_member_layout ge _events 4 /\ poll_member_layout ge _revents 6 /\
  Forall (fun entry => gateway_function_binding ge (fst entry) (snd entry)) gateway_ready_functions.

Theorem actual_gateway_ready_bindings : gateway_ready_bindings (Clight.globalenv prog).
Proof.
  destruct actual_stream_layout as (DESCRIPTOR & CONTROL & CANCEL & REST).
  destruct actual_poll_layout as (FD & EVENTS & REVENTS).
  split; [exact actual_ready_item_size |]. split; [exact actual_clock_sample_size |].
  split; [exact CONTROL |]. split; [exact CANCEL |]. split; [exact FD |]. split; [exact EVENTS |]. split; [exact REVENTS |].
  repeat constructor; apply gateway_actual_function_binding; vm_compute; reflexivity.
Qed.
