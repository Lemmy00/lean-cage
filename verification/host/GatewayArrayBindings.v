(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The array fold invokes the pinned source's own recursive parser,
   builtin append and selected release declarations with their actual SDK argument types. *)
From Stdlib Require Import List.
From compcert Require Import AST Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayObjects GatewayRegistry GatewayBindings.
Import ListNotations.

Theorem gateway_actual_array_append_binding:
  exists definition,gateway_object_api_definition gateway_api_list_append=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyList_Append definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default.
Proof.
  eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.

Theorem gateway_actual_value_release_binding:
  exists definition,gateway_object_api_definition gateway_api_decref=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_Py_DecRef definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default.
Proof.
  eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.

Theorem gateway_actual_recursive_value_binding:
  gateway_function_binding(Clight.globalenv prog)_host_value(Internal f_host_value).
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.
