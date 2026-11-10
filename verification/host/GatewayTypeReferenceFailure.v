(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Failed type construction does not steal existing source roots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects GatewayTypeRuntime
  GatewayModuleSource GatewayReferenceLedger GatewayReferenceRuntime GatewayReferenceHistory GatewayReferenceAbandon
  GatewayReferenceHistoryMove.
Import ListNotations.

Record gateway_type_reference_failure_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)(normal:mem->World->Prop):Prop:={
  gateway_type_reference_failed_from_spec:forall before world specification description after next observed,
    normal before world->gateway_source_outcome_spec specification->gateway_source_outcome_type description->
    gateway_type_spec_memory before specification description->
    gateway_type_operation backend gateway_type_from_spec[specification]before world Vnullptr after next observed->
    gateway_native_references_frame(python world)(python next)[]
}.

Theorem gateway_actual_module_type_failure_pool {World Event}(backend:gateway_backend World Event)
    python objects types allocator instances leases normal attached io native stable
    (runtime:gateway_type_runtime backend python objects types allocator instances leases normal attached io native stable)
    (references:gateway_type_reference_failure_runtime backend python objects normal)
    before world specification new initialize destroy traverse clear methods properties parameters continuation after next observed
    position ledger retired:
  gateway_history_well_formed position ledger retired->gateway_history_counts_fit ledger retired(python world)->
  normal before world->gateway_source_outcome_spec(Vptr specification Ptrofs.zero)->
  gateway_source_outcome_type(GatewayOutcomeType.gateway_outcome_description new initialize destroy traverse clear methods properties)->
  gateway_type_spec_memory before(Vptr specification Ptrofs.zero)
    (GatewayOutcomeType.gateway_outcome_description new initialize destroy traverse clear methods properties)->
  gateway_step backend(Clight.globalenv prog)
    (gateway_live(Callstate(External(EF_external "PyType_FromSpec"(mksignature[Xptr]Xptr cc_default))
      [tptr(Tstruct __5268 noattr)](tptr(Tstruct __object noattr))cc_default)[Vptr specification Ptrofs.zero]
      (module_outcome_cont parameters continuation)before)world)(gateway_primitive observed)
    (gateway_live(Returnstate Vnullptr(module_outcome_cont parameters continuation)after)next)->
  gateway_history_well_formed(S position)ledger retired /\gateway_history_counts_fit ledger retired(python next) /\
  attached after next /\
  (forall pointer,python_native_strong(python next)pointer=python_native_strong(python world)pointer).
Proof.
  intros FORMED FIT NORMAL SOURCE_SPEC SOURCE_TYPE SPECIFICATION STEP.
  assert(OPERATION:gateway_type_operation backend gateway_type_from_spec[Vptr specification Ptrofs.zero]
    before world Vnullptr after next observed).
  { eexists;split;[reflexivity|]. inversion STEP;subst;cbn[gateway_runtime_operation];eassumption. }
  pose proof(gateway_type_reference_failed_from_spec _ _ _ _ references _ _ _ _ _ _ _
    NORMAL SOURCE_SPEC SOURCE_TYPE SPECIFICATION OPERATION)as FRAME.
  assert(COUNTS:forall pointer,python_native_strong(python next)pointer=python_native_strong(python world)pointer).
  { intro pointer;apply FRAME;intro BAD;inversion BAD. }
  pose proof(@gateway_type_from_spec_effect World Event backend python objects types allocator instances leases
    normal attached io native stable runtime before world(Vptr specification Ptrofs.zero)
    (GatewayOutcomeType.gateway_outcome_description new initialize destroy traverse clear methods properties)Vnullptr after next observed
    NORMAL SPECIFICATION ltac:(cbn;lia)eq_refl OPERATION)as[ATTACHED REST].
  split;[apply gateway_history_keep_formed;exact FORMED|]. split.
  - intro pointer;rewrite COUNTS;apply FIT.
  - split;assumption.
Qed.
