(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Reaping uses the generated fixed kill, wait and sleep
   signatures. *)
From Stdlib Require Import List String.
From compcert Require Import AST Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayBindings GatewayExchangeABI.
Import ListNotations.
Local Open Scope string_scope.

Definition gateway_kill_definition:Ctypes.fundef Clight.function:=
  External(EF_external "kill"(mksignature[AST.Xint;AST.Xint]AST.Xint cc_default))[tint;tint]tint cc_default.
Definition gateway_nanosleep_definition:Ctypes.fundef Clight.function:=
  External(EF_external "nanosleep"(mksignature[AST.Xptr;AST.Xptr]AST.Xint cc_default))
    [tptr(Tstruct _timespec noattr);tptr(Tstruct _timespec noattr)]tint cc_default.

Theorem actual_gateway_reap_declarations:
  gateway_program_definition _kill global_definitions=Some(Gfun gateway_kill_definition) /\
  gateway_program_definition _nanosleep global_definitions=Some(Gfun gateway_nanosleep_definition).
Proof. split;reflexivity. Qed.

Theorem actual_gateway_kill_binding:
  gateway_function_binding(Clight.globalenv prog)_kill gateway_kill_definition.
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Theorem actual_gateway_nanosleep_binding:
  gateway_function_binding(Clight.globalenv prog)_nanosleep gateway_nanosleep_definition.
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.
