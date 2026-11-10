(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Bind the complete read producer to the maintained program. *)
From Stdlib Require Import List.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayReadyInterface
  GatewayThreadRuntime GatewayReadProducer GatewayRuntimeABI GatewayBindings GatewayStreamLayout.
Import ListNotations.

Theorem gateway_actual_read_producer {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno) :
  gateway_ready_source_producer backend(Clight.globalenv prog)io native_private stable_readonly(discipline None) ->
  gateway_read_source_producer backend(Clight.globalenv prog)io native_private stable_readonly(discipline None).
Proof.
  intro READY.
  pose proof(proj1(Forall_forall _ _)actual_gateway_transfer_functions)as TABLE.
  destruct(TABLE(_host_transfer,Internal f_host_transfer)ltac:(right;left;reflexivity))
    as(transfer_symbol & TRANSFER_SYMBOL & TRANSFER_FUNCTION).
  destruct(TABLE(_host_ready,Internal f_host_ready)ltac:(right;right;left;reflexivity))
    as(ready_symbol & READY_SYMBOL & READY_FUNCTION).
  destruct(TABLE(_PyEval_SaveThread,gateway_save_thread_definition)ltac:(right;right;right;left;reflexivity))
    as(save_symbol & SAVE_SYMBOL & SAVE_FUNCTION).
  destruct(TABLE(_recv,gateway_receive_definition)ltac:(right;right;right;right;left;reflexivity))
    as(receive_symbol & RECEIVE_SYMBOL & RECEIVE_FUNCTION).
  destruct(TABLE(___errno_location,gateway_errno_location_definition)ltac:(right;right;right;right;right;left;reflexivity))
    as(errno_symbol & ERRNO_SYMBOL & ERRNO_FUNCTION).
  destruct(TABLE(_PyEval_RestoreThread,gateway_restore_thread_definition)ltac:(right;right;right;right;right;right;left;reflexivity))
    as(restore_symbol & RESTORE_SYMBOL & RESTORE_FUNCTION).
  destruct actual_stream_layout as[DESCRIPTOR[_[_[_[_[REMAINING REST]]]]]].
  exact(gateway_read_producer_of_ready backend io native_private stable_readonly discipline thread_errno runtime
    (Clight.globalenv prog)READY transfer_symbol ready_symbol save_symbol receive_symbol errno_symbol restore_symbol
    TRANSFER_SYMBOL TRANSFER_FUNCTION READY_SYMBOL READY_FUNCTION SAVE_SYMBOL SAVE_FUNCTION RECEIVE_SYMBOL RECEIVE_FUNCTION
    ERRNO_SYMBOL ERRNO_FUNCTION RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR REMAINING).
Qed.
