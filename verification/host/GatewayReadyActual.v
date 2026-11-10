(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Bind readiness and its maintained read caller to the actual program. *)
From compcert Require Import Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadyInterface GatewayStreamInterface
  GatewayReadyBindings GatewayReadyProducer GatewayReadActual GatewayThreadRuntime.

Theorem gateway_actual_ready_producer {World Event} (backend : gateway_backend World Event) io
    native_private stable_readonly discipline thread_errno
    (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno) :
  gateway_ready_source_producer backend (Clight.globalenv prog) io native_private stable_readonly (discipline None).
Proof. exact (gateway_ready_producer_of_runtime backend (Clight.globalenv prog) io native_private stable_readonly
  discipline thread_errno runtime actual_gateway_ready_bindings). Qed.

Theorem gateway_actual_complete_read {World Event} (backend : gateway_backend World Event) io
    native_private stable_readonly discipline thread_errno
    (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno) :
  gateway_read_source_producer backend (Clight.globalenv prog) io native_private stable_readonly (discipline None).
Proof. exact (gateway_actual_read_producer backend io native_private stable_readonly discipline thread_errno runtime
  (gateway_actual_ready_producer backend io native_private stable_readonly discipline thread_errno runtime)). Qed.
