(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Numeric source-call bindings use the current maintained
   frontend and actual fixed-signature CPython SDK declarations. *)
From Stdlib Require Import List.
From compcert Require Import AST Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayObjects GatewayBindings.
Import ListNotations.

Theorem gateway_actual_number_multiply_binding:
  exists definition,gateway_object_api_definition gateway_api_number_multiply=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyNumber_Multiply definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default.
Proof. eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity]. Qed.

Theorem gateway_actual_number_add_binding:
  exists definition,gateway_object_api_definition gateway_api_number_add=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyNumber_Add definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default.
Proof. eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity]. Qed.

Theorem gateway_actual_number_negative_binding:
  exists definition,gateway_object_api_definition gateway_api_number_negative=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyNumber_Negative definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default.
Proof. eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity]. Qed.
