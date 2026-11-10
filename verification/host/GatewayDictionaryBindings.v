(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Dictionary recursion and guards use the maintained source's
   actual SDK declarations and builtin type symbol, with their precise argument ABI. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Values Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayObjects GatewayObjectInstances GatewayRegistry GatewayBindings.
Import ListNotations.

Theorem gateway_actual_dictionary_key_binding:
  exists definition,gateway_object_api_definition gateway_api_is_instance=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyObject_IsInstance definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default.
Proof.
  eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.
Theorem gateway_actual_dictionary_contains_binding:
  exists definition,gateway_object_api_definition gateway_api_dict_contains=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyDict_Contains definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default.
Proof.
  eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.
Theorem gateway_actual_dictionary_insert_binding:
  exists definition,gateway_object_api_definition gateway_api_dict_set=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyDict_SetItem definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default.
Proof.
  eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.
Theorem gateway_actual_dictionary_unicode_binding:
  exists symbol,Genv.find_symbol(Clight.globalenv prog)_PyUnicode_Type=Some symbol /\
    gateway_builtin_type_address(Clight.globalenv prog)gateway_unicode_kind(Vptr symbol Integers.Ptrofs.zero).
Proof.
  assert(DEFINITION:(prog_defmap prog)!_PyUnicode_Type=Some(Gvar v_PyUnicode_Type))by(vm_compute;reflexivity).
  destruct((proj1(Genv.find_def_symbol prog _PyUnicode_Type(Gvar v_PyUnicode_Type)))DEFINITION)as[symbol[SYMBOL VARIABLE]].
  exists symbol;split;[exact SYMBOL|constructor;exact SYMBOL].
Qed.
