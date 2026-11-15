(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A non-NULL caller crosses its actual type-check failure barrier. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayOutcomeValidationContext
  GatewayObjectInstances GatewayBuiltinTypeSource GatewayValidationTypeChecks GatewayContexts GatewaySourceCuts
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayObjectDiscipline GatewayObjectThreads GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationCheckCut.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (decimal_float : list Z -> Floats.float -> Prop) (detached : val -> mem -> World -> Prop)
    (io : Event -> option gateway_native_io) (stable : World -> block -> Z -> Prop)
    (thread_errno : World -> int) (heap_allocation : block -> Z -> Prop) (leases : World -> nat -> val -> Prop)
    (threads : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    (instances : gateway_instance_runtime backend ge python objects leases).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (original : val) (protected : block -> Z -> Prop) (source : mem) (environment : env).
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.
Context (extra : mem -> World -> Prop)
  (extra_ambient : forall before world after next, base before world -> extra before world ->
    gateway_interference backend before world after next -> extra after next)
  (extra_observer : forall before world after next, base before world -> extra before world ->
    gateway_observer_return (python world) (objects world) before (python next) (objects next) after -> extra after next).

Theorem gateway_actual_positive_validation_call object offset description kind expected class class_offset none optional continuation
    before world events value after next symbol definition :
  is_call_cont continuation -> (0 < gateway_cont_weight continuation)%nat ->
  base before world -> extra before world ->
  gateway_object_reachable captured original (Vptr object offset) ->
  gateway_object_values captured (Vptr object offset) = Some description -> gateway_object_kind description = Some kind ->
  gateway_builtin_type_address ge expected (Vptr class class_offset) ->
  (optional = Int.zero \/ optional = Int.one) -> Genv.find_symbol ge __Py_NoneStruct = Some none ->
  Genv.find_symbol ge _PyObject_IsInstance = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  gateway_object_api_definition gateway_api_is_instance = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  (forall status memory, Int.signed status <= 0 ->
    gateway_failure_when backend ge (fun _ _ => True) (Returnstate (Vint status) continuation memory)) ->
  value <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_has_type) [Vptr object offset; Vptr class class_offset; Vint optional] continuation before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists operation suffix changed following,
    events = operation ++ suffix /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_has_type) [Vptr object offset; Vptr class class_offset; Vint optional] Kstop before) world) operation
      (gateway_live (Returnstate (Vint Int.one) Kstop changed) following) /\
    base changed following /\ extra changed following /\
    ((optional = Int.one /\ Vptr object offset = Vptr none Ptrofs.zero) \/ gateway_builtin_accepts expected kind = true) /\
    gateway_steps backend ge (gateway_live (Returnstate (Vint Int.one) continuation changed) following) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros CALL WEIGHT BASE EXTRA REACHED DESCRIPTION KIND CLASS OPTIONAL NONE SYMBOL FUNCTION DEFINITION TYPE FAILURE NONNULL RUN.
  destruct (gateway_return_cut backend ge (Internal f_host_has_type)
    [Vptr object offset; Vptr class class_offset; Vint optional] continuation before world events
    (Returnstate value Kstop after) next CALL WEIGHT RUN)
    as (operation &suffix &returned &changed &following &EVENTS &OPERATION &REST).
  destruct (gateway_actual_validation_type_check backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances ledger held reserved captured original protected source environment extra extra_ambient extra_observer
    object offset description kind expected class class_offset none optional before world operation returned changed following symbol definition
    (conj BASE EXTRA) REACHED DESCRIPTION KIND CLASS OPTIONAL NONE SYMBOL FUNCTION DEFINITION TYPE OPERATION)
    as [status [RETURN POST]].
  subst returned.
  assert (POSITIVE : 0 < Int.signed status).
  { destruct (Z_le_gt_dec (Int.signed status) 0) as [BAD |GOOD]; [|lia].
    exfalso; apply NONNULL; exact (FAILURE status changed BAD changed following suffix value after next I REST). }
  destruct (POST POSITIVE) as [[GOOD EXTRA_GOOD] [SAME ACCEPT]]; subst status.
  exists operation, suffix, changed, following.
  exact (conj EVENTS (conj OPERATION (conj GOOD (conj EXTRA_GOOD (conj ACCEPT REST))))).
Qed.
End ValidationCheckCut.
