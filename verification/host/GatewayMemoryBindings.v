(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Native allocation calls use the maintained source's actual ABI bindings. *)
From compcert Require Import AST Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayBindings GatewayNativeMemory.

Theorem gateway_actual_memory_binding api :
  exists definition,gateway_memory_definition api=Some definition /\
    gateway_function_binding(Clight.globalenv prog)(gateway_memory_ident api)definition.
Proof.
  destruct api;(eexists;split;[reflexivity|apply gateway_actual_function_binding;vm_compute;reflexivity]).
Qed.
