(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Exchange lifecycle calls use their actual fixed SDK signatures. *)
From Stdlib Require Import List String.
From compcert Require Import AST Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayBindings.
Import ListNotations.
Local Open Scope string_scope.

Definition gateway_shutdown_definition:Ctypes.fundef Clight.function:=
  External(EF_external "shutdown"(mksignature[AST.Xint;AST.Xint]AST.Xint cc_default))
    [tint;tint]tint cc_default.
Definition gateway_waitpid_definition:Ctypes.fundef Clight.function:=
  External(EF_external "waitpid"(mksignature[AST.Xint;AST.Xptr;AST.Xint]AST.Xint cc_default))
    [tint;tptr tint;tint]tint cc_default.

Theorem actual_gateway_exchange_declarations:
  gateway_program_definition _shutdown global_definitions=Some(Gfun gateway_shutdown_definition) /\
  gateway_program_definition _waitpid global_definitions=Some(Gfun gateway_waitpid_definition).
Proof. split;reflexivity. Qed.

Theorem actual_gateway_shutdown_binding:
  gateway_function_binding(Clight.globalenv prog)_shutdown gateway_shutdown_definition.
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Theorem actual_gateway_waitpid_binding:
  gateway_function_binding(Clight.globalenv prog)_waitpid gateway_waitpid_definition.
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.
