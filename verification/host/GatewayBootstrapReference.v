(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Valid individual libc loader/string operations retain the
   current source reference pool, including archived unreleased allocations. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayBootstrapABI GatewayBootstrapRuntime GatewayBootstrapPython
  GatewayPython GatewayObjects GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHistory
  GatewayReferenceAbandon GatewayReferenceThreads.

Record gateway_bootstrap_reference_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_bootstrap_reference_operation:forall api arguments before world result after next observed,
    gateway_objects_ready(python world)(objects world)before->
    gateway_bootstrap_python_outputs(python world)api arguments->gateway_bootstrap_arguments_valid before api arguments->
    gateway_bootstrap_operation backend api arguments before world result after next observed->
    python next=python world /\objects next=objects world /\
    Mem.unchanged_on(fun object _=>python_runtime_owned(python world)object)before after
}.

Theorem gateway_bootstrap_reference_history {World Event}(backend:gateway_backend World Event)
    python objects(runtime:gateway_bootstrap_reference_runtime backend python objects)
    decimal_float ledger retired held api arguments before world result after next observed:
  gateway_objects_ready(python world)(objects world)before->
  gateway_history_counts_fit ledger retired(python world)->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_bootstrap_python_outputs(python world)api arguments->gateway_bootstrap_arguments_valid before api arguments->
  gateway_bootstrap_operation backend api arguments before world result after next observed->
  python next=python world /\objects next=objects world /\
  gateway_objects_ready(python next)(objects next)after /\gateway_history_counts_fit ledger retired(python next) /\
  gateway_reference_scope python objects decimal_float ledger held next /\
  Mem.unchanged_on(fun object _=>python_runtime_owned(python world)object)before after.
Proof.
  intros READY FIT SCOPE OUTPUTS VALID OPERATION.
  destruct(gateway_bootstrap_reference_operation _ _ _ runtime _ _ _ _ _ _ _ _ READY OUTPUTS VALID OPERATION)
    as[PYTHON[OBJECTS FRAME]].
  split;[exact PYTHON|]. split;[exact OBJECTS|].
  rewrite PYTHON,OBJECTS;split;[eapply gateway_objects_ready_native_frame;[exact READY|exact FRAME]|].
  split;[exact FIT|]. split;[|exact FRAME].
  unfold gateway_reference_scope,GatewayReferenceHeld.gateway_reference_held in SCOPE|-*.
  rewrite PYTHON,OBJECTS;exact SCOPE.
Qed.

(* The empty legacy view supports unchanged generic libc-only readiness leaves.
   It supplies no root or release authority and is not a RootLeases instance. *)
Theorem gateway_bootstrap_reference_readiness_view {World Event}(backend:gateway_backend World Event)
    python objects(runtime:gateway_bootstrap_reference_runtime backend python objects):
  gateway_bootstrap_python_runtime backend python objects(fun _ _ _=>False).
Proof.
  constructor;intros api arguments before world result after next observed READY OUTPUTS VALID OPERATION.
  destruct(gateway_bootstrap_reference_operation _ _ _ runtime _ _ _ _ _ _ _ _ READY OUTPUTS VALID OPERATION)
    as[PYTHON[OBJECTS FRAME]].
  split;[exact PYTHON|]. split;[exact OBJECTS|]. split;[intros ticket pointer NONE;contradiction|exact FRAME].
Qed.
