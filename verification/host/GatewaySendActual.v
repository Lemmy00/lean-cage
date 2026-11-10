(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Bind the outgoing source producer to the maintained program. *)
From Stdlib Require Import List.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayReadyInterface
  GatewayThreadRuntime GatewaySendInterface GatewaySendProducer GatewaySendReady GatewayReadyActual
  GatewayRuntimeABI GatewayBindings GatewayStreamLayout GatewayReadyOutgoing GatewayReadyBindings.
Import ListNotations.

Theorem gateway_actual_send_producer_of_no_data_send {World Event}(backend:gateway_backend World Event)io
    native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno):
  gateway_ready_no_data_send_source backend(Clight.globalenv prog)io native stable(discipline None)->
  gateway_send_source_producer backend(Clight.globalenv prog)io native stable(discipline None).
Proof.
  intro NO_DATA_SEND.
  pose proof(proj1(Forall_forall _ _)actual_gateway_transfer_functions)as TABLE.
  destruct(TABLE(_host_ready,Internal f_host_ready)ltac:(cbn;tauto))as(ready_symbol&READY_SYMBOL&READY_FUNCTION).
  destruct(TABLE(_PyEval_SaveThread,gateway_save_thread_definition)ltac:(cbn;tauto))as(save_symbol&SAVE_SYMBOL&SAVE_FUNCTION).
  destruct(TABLE(___errno_location,gateway_errno_location_definition)ltac:(cbn;tauto))as(errno_symbol&ERRNO_SYMBOL&ERRNO_FUNCTION).
  destruct(TABLE(_PyEval_RestoreThread,gateway_restore_thread_definition)ltac:(cbn;tauto))as(restore_symbol&RESTORE_SYMBOL&RESTORE_FUNCTION).
  pose proof(proj1(Forall_forall _ _)actual_gateway_runtime_functions)as RUNTIME.
  destruct(RUNTIME(_send,gateway_send_definition)ltac:(cbn;tauto))as(send_symbol&SEND_SYMBOL&SEND_FUNCTION).
  destruct actual_stream_layout as[DESCRIPTOR REST].
  exact(gateway_send_producer_of_ready backend io native stable discipline thread_errno runtime(Clight.globalenv prog)
    (gateway_actual_ready_producer backend io native stable discipline thread_errno runtime)NO_DATA_SEND
    ready_symbol save_symbol send_symbol errno_symbol restore_symbol READY_SYMBOL READY_FUNCTION SAVE_SYMBOL SAVE_FUNCTION
    SEND_SYMBOL SEND_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR).
Qed.

Theorem gateway_actual_send_producer {World Event}(backend:gateway_backend World Event)io
    native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno):
  gateway_send_source_producer backend(Clight.globalenv prog)io native stable(discipline None).
Proof.
  apply gateway_actual_send_producer_of_no_data_send with(thread_errno:=thread_errno);[exact runtime|].
  exact(gateway_actual_ready_no_data_send backend(Clight.globalenv prog)io native stable discipline thread_errno runtime
    actual_gateway_ready_bindings).
Qed.
