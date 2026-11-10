(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A returned integer excludes failed multiply/add calls through
   the actual intervening releases, without assuming failed SDK calls preserve readiness. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberIntegerStructure GatewayNumberIntegerCalls GatewayNumberIterationFailure
  GatewayValueReturns GatewaySourcePaths GatewayContexts GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_number_scaled_success_nonnull {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters current returned before world events value after next symbol definition:
  parameters!_value__1=Some current->gateway_object_pointer_value current->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_steps backend ge(gateway_live(Returnstate returned(number_integer_multiply_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->returned<>Vnullptr.
Proof.
  intros CURRENT POINTER SYMBOL FUNCTION TYPE RUN NONNULL NULL;subst returned.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_number_old_value_release_path backend ge(fun _ _=>True)parameters current Vnullptr before symbol definition
    CLOSED CURRENT POINTER SYMBOL FUNCTION TYPE)as(called_parameters &PATH &SCALED &UNCHANGED).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as(prefix &rest &called &called_world &EVENTS &QUIET &PREFIX &READY &FROM_RELEASE).
  destruct(gateway_return_cut backend ge definition[current](number_integer_release_value_cont called_parameters)
    called called_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &suffix &ignored &changed &following &REST_EVENTS &RELEASE &REST).
  apply NONNULL;exact(gateway_number_null_scaled_denied backend ge called_parameters ignored changed SCALED changed following suffix value after next REST).
Qed.

Theorem gateway_number_sum_success_nonnull {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters scaled part returned before world events value after next symbol definition:
  parameters!_scaled=Some scaled->gateway_object_pointer_value scaled->
  parameters!_part=Some part->gateway_object_pointer_value part->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_steps backend ge(gateway_live(Returnstate returned(number_integer_add_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->returned<>Vnullptr.
Proof.
  intros SCALED SCALED_POINTER PART PART_POINTER SYMBOL FUNCTION TYPE RUN NONNULL NULL;subst returned.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_number_scaled_release_path backend ge(fun _ _=>True)parameters scaled Vnullptr before symbol definition
    CLOSED SCALED SCALED_POINTER SYMBOL FUNCTION TYPE)as(called_parameters &PATH &VALUE &UNCHANGED).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as(prefix &rest &called &called_world &EVENTS &QUIET &PREFIX &READY &FROM_RELEASE).
  destruct(gateway_return_cut backend ge definition[scaled](number_integer_release_scaled_cont called_parameters)
    called called_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &suffix &ignored &changed &following &REST_EVENTS &RELEASE &REST).
  pose proof(gateway_number_part_release_path backend ge(fun _ _=>True)called_parameters part ignored changed symbol definition
    CLOSED ltac:(rewrite UNCHANGED by discriminate;exact PART)PART_POINTER SYMBOL FUNCTION TYPE)as PART_PATH.
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PART_PATH changed following suffix value after next I REST)
    as(part_prefix &from_part &part_before &part_world &PART_EVENTS &PART_QUIET &PART_PREFIX &PART_READY &FROM_PART).
  destruct(gateway_return_cut backend ge definition[part](number_integer_release_part_cont called_parameters)
    part_before part_world from_part(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_PART)
    as(part_releasing &final_suffix &part_ignored &part_after &part_next &FROM_PART_EVENTS &PART_RELEASE &FINAL).
  apply NONNULL;exact(gateway_number_null_sum_denied backend ge called_parameters part_ignored part_after VALUE part_after part_next final_suffix value after next FINAL).
Qed.
