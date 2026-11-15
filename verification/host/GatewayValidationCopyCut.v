(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual iterator EOF reaches the private copy with the SAME owned graph. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayOutcomeValidationContext
  GatewayOutcomeFilesSource GatewayOutcomeFilesIteration GatewayOutcomeCopySource GatewaySourcePaths GatewayFramedRuntime
  GatewayObjectDiscipline GatewayObjectThreads GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_validation_eof_copy {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    ledger held reserved captured data data_offset protected source environment parameters before world events value after next symbol definition :
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured (Vptr data data_offset)
    protected source environment before world ->
  parameters ! _data = Some (Vptr data data_offset) -> environment ! _PyDict_Copy = None ->
  Genv.find_symbol ge _PyDict_Copy = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] (tptr (Tstruct __object noattr)) cc_default ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint Int.zero) (gateway_validation_next_cont environment parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix suffix memory current,
    events = prefix ++ suffix /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vint Int.zero) (gateway_validation_next_cont environment parameters) before) world) prefix
      (gateway_live (Callstate definition [Vptr data data_offset]
        (gateway_outcome_copy_cont environment (set_opttemp (Some _t'15) (Vint Int.zero) parameters)) memory) current) /\
    gateway_outcome_validation_context python objects decimal_float ledger held reserved captured (Vptr data data_offset)
      protected source environment memory current /\
    gateway_steps backend ge
      (gateway_live (Callstate definition [Vptr data data_offset]
        (gateway_outcome_copy_cont environment (set_opttemp (Some _t'15) (Vint Int.zero) parameters)) memory) current) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros CONTEXT DATA LOCAL SYMBOL FUNCTION TYPE RUN.
  set (property := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured
    (Vptr data data_offset) protected source environment).
  pose proof (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime references ledger held reserved captured (Vptr data data_offset) protected source environment) as CLOSED.
  pose proof (gateway_validation_iterator_copy backend ge property environment parameters before data data_offset symbol definition
    CLOSED DATA LOCAL SYMBOL FUNCTION TYPE) as PATH.
  destruct (gateway_source_path_cut backend ge _ _ _ property _ property PATH before world events value after next CONTEXT RUN)
    as (prefix &suffix &memory &current &EVENTS &QUIET &PREFIX &READY &SUFFIX).
  exists prefix, suffix, memory, current; auto.
Qed.
