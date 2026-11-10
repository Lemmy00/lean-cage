(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual source definitions supply each callable runtime symbol. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Values Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRuntimeABI.
Import ListNotations.

Definition gateway_function_binding(ge:Clight.genv)identifier definition :Prop:=
  exists symbol,Genv.find_symbol ge identifier=Some symbol /\Genv.find_funct_ptr ge symbol=Some definition.

Lemma gateway_actual_function_binding identifier definition :
  (prog_defmap prog)!identifier=Some(Gfun definition) ->
  gateway_function_binding(Clight.globalenv prog)identifier definition.
Proof.
  intro DEFINITION.
  destruct((proj1(Genv.find_def_symbol prog identifier(Gfun definition)))DEFINITION)
    as[symbol[SYMBOL FUNCTION]].
  exists symbol;split;[exact SYMBOL|apply Genv.find_funct_ptr_iff;exact FUNCTION].
Qed.

Definition gateway_transfer_functions :list(ident*Ctypes.fundef Clight.function):=
  [(_host_read,Internal f_host_read);(_host_transfer,Internal f_host_transfer);(_host_ready,Internal f_host_ready);
   (_PyEval_SaveThread,gateway_save_thread_definition);(_recv,gateway_receive_definition);
   (___errno_location,gateway_errno_location_definition);(_PyEval_RestoreThread,gateway_restore_thread_definition)].

Theorem actual_gateway_transfer_functions :
  Forall(fun entry=>gateway_function_binding(Clight.globalenv prog)(fst entry)(snd entry))gateway_transfer_functions.
Proof.
  repeat constructor;apply gateway_actual_function_binding;vm_compute;reflexivity.
Qed.

Definition gateway_runtime_functions :list(ident*Ctypes.fundef Clight.function):=
  [(_clock_gettime,gateway_clock_gettime_definition);(_send,gateway_send_definition);
   (_poll,gateway_poll_definition);(_PyErr_CheckSignals,gateway_check_signals_definition);
   (_PyErr_SetString,gateway_set_error_definition);(_PyErr_SetFromErrno,gateway_errno_error_definition)].

Theorem actual_gateway_runtime_functions :
  Forall(fun entry=>gateway_function_binding(Clight.globalenv prog)(fst entry)(snd entry))gateway_runtime_functions.
Proof.
  repeat constructor;apply gateway_actual_function_binding;vm_compute;reflexivity.
Qed.
