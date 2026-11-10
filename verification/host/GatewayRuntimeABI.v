(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Match individual runtime contracts to actual SDK declarations. *)
From Stdlib Require Import List String.
From compcert Require Import AST Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry.
Import ListNotations.
Local Open Scope string_scope.

Definition gateway_clock_gettime_definition:Ctypes.fundef Clight.function:=
  External(EF_external "clock_gettime"(mksignature[AST.Xint;AST.Xptr]AST.Xint cc_default))
    [tint;tptr(Tstruct _timespec noattr)]tint cc_default.
Definition gateway_send_definition:Ctypes.fundef Clight.function:=
  External(EF_external "send"(mksignature[AST.Xint;AST.Xptr;AST.Xlong;AST.Xint]AST.Xlong cc_default))
    [tint;tptr tvoid;tulong;tint]tlong cc_default.
Definition gateway_receive_definition:Ctypes.fundef Clight.function:=
  External(EF_external "recv"(mksignature[AST.Xint;AST.Xptr;AST.Xlong;AST.Xint]AST.Xlong cc_default))
    [tint;tptr tvoid;tulong;tint]tlong cc_default.
Definition gateway_poll_definition:Ctypes.fundef Clight.function:=
  External(EF_external "poll"(mksignature[AST.Xptr;AST.Xlong;AST.Xint]AST.Xint cc_default))
    [tptr(Tstruct _pollfd noattr);tulong;tint]tint cc_default.
Definition gateway_errno_location_definition:Ctypes.fundef Clight.function:=
  External(EF_external "__errno_location"(mksignature[]AST.Xptr cc_default))[] (tptr tint)cc_default.
Definition gateway_save_thread_definition:Ctypes.fundef Clight.function:=
  External(EF_external "PyEval_SaveThread"(mksignature[]AST.Xptr cc_default))[]
    (tptr(Tstruct __ts noattr))cc_default.
Definition gateway_restore_thread_definition:Ctypes.fundef Clight.function:=
  External(EF_external "PyEval_RestoreThread"(mksignature[AST.Xptr]AST.Xvoid cc_default))
    [tptr(Tstruct __ts noattr)]tvoid cc_default.
Definition gateway_check_signals_definition:Ctypes.fundef Clight.function:=
  External(EF_external "PyErr_CheckSignals"(mksignature[]AST.Xint cc_default))[]tint cc_default.
Definition gateway_set_error_definition:Ctypes.fundef Clight.function:=
  External(EF_external "PyErr_SetString"(mksignature[AST.Xptr;AST.Xptr]AST.Xvoid cc_default))
    [tptr(Tstruct __object noattr);tptr tschar]tvoid cc_default.
Definition gateway_errno_error_definition:Ctypes.fundef Clight.function:=
  External(EF_external "PyErr_SetFromErrno"(mksignature[AST.Xptr]AST.Xptr cc_default))
    [tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default.

Theorem actual_gateway_runtime_declarations :
  gateway_program_definition _clock_gettime global_definitions=Some(Gfun gateway_clock_gettime_definition) /\
  gateway_program_definition _send global_definitions=Some(Gfun gateway_send_definition) /\
  gateway_program_definition _recv global_definitions=Some(Gfun gateway_receive_definition) /\
  gateway_program_definition _poll global_definitions=Some(Gfun gateway_poll_definition) /\
  gateway_program_definition ___errno_location global_definitions=Some(Gfun gateway_errno_location_definition) /\
  gateway_program_definition _PyEval_SaveThread global_definitions=Some(Gfun gateway_save_thread_definition) /\
  gateway_program_definition _PyEval_RestoreThread global_definitions=Some(Gfun gateway_restore_thread_definition) /\
  gateway_program_definition _PyErr_CheckSignals global_definitions=Some(Gfun gateway_check_signals_definition) /\
  gateway_program_definition _PyErr_SetString global_definitions=Some(Gfun gateway_set_error_definition) /\
  gateway_program_definition _PyErr_SetFromErrno global_definitions=Some(Gfun gateway_errno_error_definition).
Proof. repeat split;reflexivity. Qed.

Theorem actual_gateway_runtime_program_definitions identifier definition :
  gateway_program_definition identifier global_definitions=Some(Gfun definition) ->
  In(identifier,Gfun definition)(prog_defs prog).
Proof. rewrite gateway_actual_program_definitions;apply gateway_program_definition_present. Qed.
