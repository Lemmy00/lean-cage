(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real Workspace return transfers its selected instance credit and retained observations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts ClightSteps LocalAccess StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayTypeRuntime GatewayOutcomeAllocation GatewayOwnedOutcomeReturn GatewayOutcomeViewReturn GatewayOutcomeFields GatewayOutcomeMetadata
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceMoves GatewayReferenceCapture GatewayReferenceExecution
  GatewayReferenceFrames GatewayReferenceContextReturns GatewayReferenceThreads GatewayLocalRuntime GatewayScopedMemory GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayWorkspaceOutcomeSource GatewayReturnScope GatewayPrimitiveCalls GatewayReadonly.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_workspace_returned_outcome {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io
      (fun current object=>gateway_native_private(python current)object)stable)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    context environment parameters object copy class ledger outcome_ticket held reserved fields wires metadata_field metadata wire
    before world events value after next:
  is_call_cont context->parameters!_outcome=Some(Vptr object Ptrofs.zero)->gateway_reference_ledger_well_formed ledger->
  gateway_reference_source_bound ge(plug_state(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters before)context)ledger->
  gateway_native_environment(fun current object=>gateway_native_private(python current)object)world before environment->
  gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class ledger
    (gateway_reference_temporary(gateway_reference_depth context) _outcome)outcome_ticket held before world->
  gateway_outcome_fields_view python objects decimal_float copy fields wires world->
  gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_steps backend ge
    (gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final,
    value=Vptr object Ptrofs.zero /\gateway_reference_ledger_well_formed final /\
    gateway_reference_apply(gateway_reference_move(gateway_reference_temporary(gateway_reference_depth context) _outcome)(gateway_reference_result(gateway_reference_depth context)))
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return context environment parameters before)world)
      (gateway_reference_valid ledger)events(gateway_live(Returnstate value context after)next)(gateway_reference_valid final) /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class final
      (gateway_reference_result(gateway_reference_depth context))outcome_ticket held after next /\
    gateway_reference_place_value ge(Returnstate value context after)(gateway_reference_result(gateway_reference_depth context))value /\
    gateway_outcome_fields_view python objects decimal_float copy fields wires next /\
    gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat).
Proof.
  intros CALL OUTCOME WELL BOUND ENVIRONMENT CONTEXT FIELDS METADATA BUDGET RUN.
  assert(VACANT:gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries ledger)=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;specialize(BOUND entry MEMBER);rewrite OWNER in BOUND;exact BOUND. }
  set(view:=fun current=>gateway_outcome_fields_view python objects decimal_float copy fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire current /\
    forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python current)pointer)%nat).
  assert(VIEW_FRAME:forall first last,view first->gateway_reference_thread_effect python objects first last->view last).
  { intros first last[FIELD_VIEWS[META_VIEW COUNTED]]EFFECT;split;[eapply gateway_outcome_fields_view_frame;eassumption|].
    split;[eapply gateway_outcome_metadata_view_frame;eassumption|].
    intro pointer;specialize(COUNTED pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  assert(AVOIDS:gateway_environment_avoids(gateway_outcome_cell_region object)environment).
  { intros identifier candidate ty position LOOK[SAME RANGE];subst candidate.
    destruct(ENVIRONMENT identifier object ty LOOK)as[LIVE NATIVE].
    destruct CONTEXT as[_[[_[RUNTIME REST]]MORE]];exact(NATIVE RUNTIME). }
  assert(INITIAL:gateway_owned_outcome_return_state python objects instances owned decimal_float object copy class ledger
    (gateway_reference_temporary(gateway_reference_depth context) _outcome)outcome_ticket held
    (gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters before)world)).
  { split;[split;[reflexivity|split;[reflexivity|exact ENVIRONMENT]]|].
    split;[split;[reflexivity|split;[reflexivity|exact AVOIDS]]|exact CONTEXT]. }
  destruct(gateway_outcome_return_view_run backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation runtime allocations reference_threads view VIEW_FRAME object copy class ledger
    (gateway_reference_temporary(gateway_reference_depth context) _outcome)outcome_ticket held _ events _ INITIAL(conj FIELDS(conj METADATA BUDGET))RUN)
    as[[_[_ FINAL_CONTEXT]][FINAL_FIELDS[FINAL_META FINAL_BUDGET]]].
  destruct(gateway_reference_context_source_return backend ge context f_host_workspace_execute
    (Etempvar _outcome(tptr(Tstruct __object noattr)))_outcome Kstop environment parameters(Vptr object Ptrofs.zero)
    before world events value after next ledger outcome_ticket eq_refl eq_refl
    ltac:(intros;apply old_expression_value,value_temp;exact OUTCOME)
    ltac:(intros memory converted CAST;cbn in CAST;inversion CAST;reflexivity)WELL
    (proj1(proj2(proj2(proj2(proj2 CONTEXT)))))VACANT RUN)
    as(final &SAME &EXECUTION &MOVE &FINAL_WELL &FINAL_OWNER &COUNTS).
  cbn[plug_cont]in MOVE,FINAL_OWNER,COUNTS.
  destruct FINAL_CONTEXT as[NORMAL[CELL[LOAD[CLASS[OWNER SCOPE]]]]].
  destruct(gateway_reference_move_scope python objects decimal_float ledger(gateway_reference_temporary(gateway_reference_depth context) _outcome)(gateway_reference_result(gateway_reference_depth context))
    outcome_ticket(Vptr object Ptrofs.zero)held next WELL OWNER VACANT SCOPE)
    as(moved &MOVE_AGAIN &MOVED_WELL &MOVED_OWNER &MOVED_SCOPE &MOVED_COUNTS &RETAINED).
  rewrite MOVE in MOVE_AGAIN;injection MOVE_AGAIN as IDENTICAL;subst moved.
  exists final;split;[exact SAME|]. split;[exact FINAL_WELL|]. split;[exact MOVE|]. split.
  - exact(gateway_reference_context_execution_plugs backend ge context _ _ _ _ _ CALL EXECUTION).
  - split;[exact(conj NORMAL(conj CELL(conj LOAD(conj CLASS(conj MOVED_OWNER MOVED_SCOPE)))))|]. split.
    + apply gateway_reference_result_binding.
    + split;[exact FINAL_FIELDS|]. split;[exact FINAL_META|]. intro pointer;rewrite COUNTS;apply FINAL_BUDGET.
Qed.
