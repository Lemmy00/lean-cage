(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Observation uses the actual error-preserving metadata lookup ABI. *)
From Stdlib Require Import List Strings.String.
From compcert Require Import AST Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayBindings.
Import ListNotations.

Definition gateway_observation_key_definition:Ctypes.fundef Clight.function:=
  External(EF_external "PyUnicode_FromString"(mksignature[Xptr]Xptr cc_default))
    [tptr tschar](tptr(Tstruct __object noattr))cc_default.

Definition gateway_observation_lookup_definition:Ctypes.fundef Clight.function:=
  External(EF_external "PyDict_GetItemWithError"(mksignature[Xptr;Xptr]Xptr cc_default))
    [tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]
    (tptr(Tstruct __object noattr))cc_default.

Definition gateway_observation_error_definition:Ctypes.fundef Clight.function:=
  External(EF_external "PyErr_Occurred"(mksignature[]Xptr cc_default))
    [](tptr(Tstruct __object noattr))cc_default.

Definition gateway_observation_functions:list(ident*Ctypes.fundef Clight.function):=
  [(_PyUnicode_FromString,gateway_observation_key_definition);
   (_PyDict_GetItemWithError,gateway_observation_lookup_definition);
   (_PyErr_Occurred,gateway_observation_error_definition)].

Theorem gateway_actual_observation_functions:
  Forall(fun entry=>gateway_function_binding(Clight.globalenv prog)(fst entry)(snd entry))
    gateway_observation_functions.
Proof. repeat constructor;apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.
