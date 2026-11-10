(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Allocation failure invokes the actual SDK error function. *)
From compcert Require Import AST Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayBindings GatewayNoMemory.

Theorem gateway_actual_no_memory_binding :
  gateway_function_binding(Clight.globalenv prog)_PyErr_NoMemory gateway_no_memory_definition.
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.
