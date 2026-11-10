(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Decoder calls use the maintained program's actual callable symbols. *)
From Stdlib Require Import List.
From compcert Require Import AST Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayBindings.
Import ListNotations.

Definition gateway_value_functions:list(ident*Ctypes.fundef Clight.function):=
  [(_host_word,Internal f_host_word);(_host_get64,Internal f_host_get64)].

Theorem actual_gateway_value_functions :
  Forall(fun entry=>gateway_function_binding(Clight.globalenv prog)(fst entry)(snd entry))gateway_value_functions.
Proof. repeat constructor;apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.
