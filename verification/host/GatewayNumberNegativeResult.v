(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real negation result survives its ignored old-value
   release and source assignment, including the NULL allocation-failure case. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberSignSource GatewayValueReturns GatewaySourcePaths GatewayContexts GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_number_negative_result_identity {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters current returned before world events value after next symbol definition:
  parameters!_value__1=Some current->gateway_object_pointer_value current->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_steps backend ge(gateway_live(Returnstate returned(number_sign_negative_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=returned.
Proof.
  intros CURRENT POINTER SYMBOL FUNCTION TYPE RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_number_negative_release_path backend ge(fun _ _=>True)parameters current returned before symbol definition
    CLOSED CURRENT POINTER SYMBOL FUNCTION TYPE)as(called_parameters &PATH &SELECTED &UNCHANGED).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as(prefix &rest &called &called_world &EVENTS &QUIET &PREFIX &READY &FROM_RELEASE).
  destruct(gateway_return_cut backend ge definition[current](number_sign_old_cont called_parameters)called called_world rest
    (Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &suffix &ignored &changed &following &REST_EVENTS &RELEASE &REST).
  exact(gateway_number_negative_return_identity backend ge called_parameters returned ignored changed following suffix value after next SELECTED REST).
Qed.
