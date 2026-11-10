(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The inline None return owns the reference created by its actual IncRef. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayObjectConstants GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueStack
  GatewayValueTag GatewayValueNull GatewayValueNullSource GatewayValueRegions GatewayValueEnvironment
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceNoneRun GatewayThreadInvariant GatewayReturnRuntime GatewayCallerReturns GatewayObjectRuns
  GatewayObjectEvents GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_null_branch {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation decimal_float
    (runtime:gateway_thread_runtime backend io(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    context ledger held slots arguments initial stream_block stream_offset final_stream readonly original
    before world events value after next none_symbol reference_symbol descriptor:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries ledger)=None->
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero)->
  Genv.find_symbol ge __Py_NoneStruct=Some none_symbol->Genv.find_symbol ge _Py_IncRef=Some reference_symbol->
  Genv.find_funct_ptr ge reference_symbol=Some python_incref_definition->
  gateway_value_tagged(fun world object=>gateway_native_private(python world)object)stable
    (gateway_thread_invariant_discipline(gateway_python_discipline python objects detached)
      (gateway_reference_scope python objects decimal_float ledger held))
    slots stream_block stream_offset final_stream readonly original Int64.zero before world->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next)->
  exists final,
    value=Vptr none_symbol Ptrofs.zero /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)value /\
    gateway_reference_place_value ge(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value gateway_none_object|}])next /\
    gateway_value_heap decimal_float(objects next)value LeanCage_Host_GatewayResponseCode_Value_null /\
    gateway_python_discipline python objects detached None after next /\gateway_received_bytes io descriptor events=[] /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_result(gateway_reference_depth context))value)
      (gateway_reference_valid ledger)=gateway_reference_valid final.
Proof.
  intros CALL FORMED VACANT CONSTANTS NONE REFERENCE FUNCTION INPUT RUN.
  set(native:=fun world object=>gateway_native_private(python world)object).
  set(base:=gateway_python_discipline python objects detached).
  set(augmented:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation
    python objects decimal_float reference_threads ledger held runtime)as SCOPED_RUNTIME.
  set(property:=gateway_value_tagged native stable augmented slots stream_block stream_offset final_stream readonly original Int64.zero).
  pose proof(gateway_value_tagged_ambient backend io native stable augmented thread_errno SCOPED_RUNTIME
    slots stream_block stream_offset final_stream readonly original Int64.zero)as CLOSED.
  destruct(gateway_actual_null_reference backend ge property slots arguments initial before world events value after next
    none_symbol reference_symbol python_incref_definition CLOSED ltac:(intros;exact(proj2 H))
    NONE REFERENCE FUNCTION eq_refl INPUT RUN)
    as(prefix &reference &suffix &called &called_world &result &returned &returned_world &
      EVENTS &VALUE &QUIET &PREFIX &CALLED &API_RUN &SUFFIX).
  pose proof(gateway_value_active_environment native stable augmented slots stream_block stream_offset final_stream readonly original
    called called_world(proj1 CALLED))as[[SIDE[FIT HELD]]ENVIRONMENT].
  (* This inline expression has no object-valued C temporary. The actual IncRef
     reserves the caller result owner; physical result binding is proved only
     after the same source return below. *)
  destruct(gateway_reference_actual_none_run backend ge python objects detached io stable thread_errno heap_allocation decimal_float
    runtime references reference_threads ledger(gateway_reference_result(gateway_reference_depth context))held
    (Vptr none_symbol Ptrofs.zero)(gateway_value_environment slots)called called_world reference result returned returned_world
    FORMED FIT VACANT HELD CONSTANTS(conj SIDE ENVIRONMENT)API_RUN)
    as[final[MINT[WELL[OWNED[SCOPE RETURN_ENV]]]]].
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation
    python objects decimal_float reference_threads final
    (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=Vptr none_symbol Ptrofs.zero;
      gateway_held_view:=gateway_held_scalar_value gateway_none_object|}])runtime)as RETURN_RUNTIME.
  assert(READY:gateway_return_environment native
    (gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=Vptr none_symbol Ptrofs.zero;
        gateway_held_view:=gateway_held_scalar_value gateway_none_object|}])))
    None(gateway_value_environment slots)returned returned_world).
  { split;[split;[exact(proj1 RETURN_ENV)|exact SCOPE]|exact(proj2 RETURN_ENV)]. }
  destruct(gateway_actual_caller_return_side backend ge io native stable _ thread_errno RETURN_RUNTIME
    None f_host_value None(gateway_value_environment slots)(gateway_value_none_parameters arguments initial)
    (match gateway_value_none_return with Sreturn expression=>expression|_=>None end)
    (Kseq gateway_value_after_null Kstop)returned returned_world suffix result value after next
    eq_refl READY SUFFIX)as[[FINAL_SIDE FINAL_SCOPE]TAIL_QUIET].
  rewrite VALUE in *.
  assert(LOOKUP:gateway_object_values(objects next)(Vptr none_symbol Ptrofs.zero)=Some gateway_none_object).
  { pose proof(proj2 FINAL_SCOPE)as CAPTURED;apply Forall_app in CAPTURED;destruct CAPTURED as[OLD NEW].
    destruct(Forall_inv NEW)as[OWNED_FINAL[PRIVATE[DESTROY[LOOKUP CHILDREN]]]];exact LOOKUP. }
  exists final;split;[reflexivity|]. split;[exact WELL|]. split;[exact OWNED|].
  split;[apply gateway_reference_result_binding|]. split;[exact FINAL_SCOPE|].
  split;[apply gateway_heap_null;exact LOOKUP|]. split;[exact FINAL_SIDE|]. split;[|exact MINT].
  rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io descriptor prefix QUIET),
    (gateway_object_run_no_direct_receive backend ge io gateway_api_incref python_incref_definition[Vptr none_symbol Ptrofs.zero]
      called called_world reference result returned returned_world descriptor projection eq_refl API_RUN),
    (gateway_quiet_received io descriptor suffix TAIL_QUIET);reflexivity.
Qed.
