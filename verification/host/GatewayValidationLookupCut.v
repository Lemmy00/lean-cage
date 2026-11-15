(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Required lookups in a non-NULL result borrow from its original received dictionary. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayBuiltinValidation GatewayObjectExecution
  GatewayContexts GatewaySourceCuts GatewayFramedRuntime GatewayReturnScope
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationLookupCut.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (decimal_float : list Z -> Floats.float -> Prop) (detached : val -> mem -> World -> Prop)
    (io : Event -> option gateway_native_io) (stable : World -> block -> Z -> Prop)
    (thread_errno : World -> int) (heap_allocation : block -> Z -> Prop)
    (threads : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    (containers : gateway_container_runtime backend python objects).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (original : val) (protected : block -> Z -> Prop) (source : mem) (environment : env).
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.

Theorem gateway_actual_validation_lookup definition name characters fields continuation before world events value after next :
  gateway_object_api_definition gateway_api_dict_get_string = Some definition ->
  is_call_cont continuation -> (0 < gateway_cont_weight continuation)%nat ->
  gateway_object_values captured original = Some (gateway_dict_object fields) ->
  (forall memory current, base memory current -> gateway_object_name memory name characters) ->
  (forall memory, gateway_failure_when backend ge (fun _ _ => True) (Returnstate Vnullptr continuation memory)) ->
  base before world -> value <> Vnullptr ->
  gateway_steps backend ge (gateway_live (Callstate definition [original; name] continuation before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists operation suffix memory current field,
    events = operation ++ suffix /\ gateway_dictionary_lookup characters fields = Some field /\
    gateway_object_reachable captured original (gateway_dictionary_value field) /\
    gateway_steps backend ge (gateway_live (Callstate definition [original; name] Kstop before) world) operation
      (gateway_live (Returnstate (gateway_dictionary_value field) Kstop memory) current) /\
    base memory current /\
    gateway_steps backend ge (gateway_live (Returnstate (gateway_dictionary_value field) continuation memory) current) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros DEFINITION CALL WEIGHT FIELDS NAME FAILURE BASE NONNULL RUN.
  assert (CLOSED : gateway_ambient_closed backend base).
  { exact (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured original protected source environment). }
  destruct (gateway_return_cut backend ge definition [original; name] continuation before world events
    (Returnstate value Kstop after) next CALL WEIGHT RUN)
    as (operation &suffix &result &memory &current &EVENTS &OPERATION &REST).
  assert (RESULT_NONNULL : result <> Vnullptr).
  { intro NULL; subst result; apply NONNULL; exact (FAILURE memory memory current suffix value after next I REST). }
  destruct (gateway_actual_object_operation backend ge gateway_api_dict_get_string definition [original; name] base
    before world operation result memory current DEFINITION CLOSED BASE OPERATION)
    as (pending &tail &called &called_world &changed &changed_world &observed &OPERATION_EVENTS &CALLED &ACTUAL &PREFIX &TAIL).
  destruct (gateway_validation_lookup_context backend python objects decimal_float ledger held reserved captured original protected source environment containers
    fields called called_world name characters result changed changed_world observed CALLED FIELDS (NAME _ _ CALLED) ACTUAL RESULT_NONNULL)
    as (field &LOOKUP &RESULT &REACHED &CHANGED).
  destruct (gateway_terminal_return_scope backend ge base result CLOSED changed changed_world tail result memory current CHANGED TAIL)
    as [SAME GOOD].
  subst result; exists operation, suffix, memory, current, field.
  exact (conj EVENTS (conj LOOKUP (conj REACHED (conj OPERATION (conj GOOD REST))))).
Qed.
End ValidationLookupCut.
