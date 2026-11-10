(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Primitive value branches use their actual SDK function bindings. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayBindings GatewayObjects GatewayPython.
Import ListNotations.

Theorem actual_gateway_none_binding :
  exists symbol,Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some symbol.
Proof.
  destruct((proj1(Genv.find_def_symbol prog __Py_NoneStruct(Gvar v__Py_NoneStruct)))
    ltac:(vm_compute;reflexivity))as[symbol[SYMBOL DEFINITION]];exists symbol;exact SYMBOL.
Qed.

Theorem actual_gateway_incref_binding :
  gateway_function_binding(Clight.globalenv prog)_Py_IncRef python_incref_definition.
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Theorem actual_gateway_boolean_binding :
  exists definition,gateway_object_api_definition gateway_api_bool=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyBool_FromLong definition /\
    type_of_fundef definition=Tfunction[Ctypesdefs.tlong](Ctypesdefs.tptr(Tstruct __object noattr))cc_default.
Proof.
  eexists;split;[vm_compute;reflexivity|]. split.
  - apply gateway_actual_function_binding;vm_compute;reflexivity.
  - reflexivity.
Qed.
