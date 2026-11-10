(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The zero-tag source branch returns its actual retained None reference. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayRootLeases GatewayObjectConstants GatewayObjectDiscipline GatewayObjectThreads GatewayValue
  GatewayValueEntry GatewayValueStack GatewayValueTag GatewayValueNull GatewayValueNullSource GatewayValueRegions
  GatewayValueEnvironment GatewayNoneReferenceRun GatewayReturnRuntime GatewayCallerReturns GatewayObjectRuns
  GatewayObjectEvents GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section NullHeap.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->BinNums.Z->Prop)
  (decimal_float:list BinNums.Z->Floats.float->Prop)(leases:World->nat->Values.val->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (references:gateway_reference_runtime backend python objects)
  (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
  (object_threads:gateway_object_thread_contract backend native stable base heap_allocation python objects leases)
  (projection:gateway_direct_io_projection backend io).

Theorem gateway_actual_null_branch slots arguments initial stream_block stream_offset final_stream readonly original
    before world events value after next none_symbol reference_symbol descriptor :
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero) ->
  Genv.find_symbol ge __Py_NoneStruct=Some none_symbol ->
  Genv.find_symbol ge _Py_IncRef=Some reference_symbol ->
  Genv.find_funct_ptr ge reference_symbol=Some python_incref_definition ->
  gateway_value_tagged native stable base slots stream_block stream_offset final_stream readonly original Int64.zero
    before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->
  exists ticket,value=Vptr none_symbol Ptrofs.zero /\
    gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value gateway_none_object|}]next /\
    gateway_value_heap decimal_float(objects next)value LeanCage_Host_GatewayResponseCode_Value_null /\
    base None after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros CONSTANTS NONE REFERENCE FUNCTION INPUT RUN.
  set(property:=gateway_value_tagged native stable base slots stream_block stream_offset final_stream readonly original Int64.zero).
  pose proof(gateway_value_tagged_ambient backend io native stable base thread_errno runtime
    slots stream_block stream_offset final_stream readonly original Int64.zero)as CLOSED.
  destruct(gateway_actual_null_reference backend ge property slots arguments initial before world events value after next
    none_symbol reference_symbol python_incref_definition CLOSED ltac:(intros;exact(proj2 H))
    NONE REFERENCE FUNCTION eq_refl INPUT RUN)
    as(prefix &reference &suffix &called &called_world &result &returned &returned_world &
      EVENTS &VALUE &QUIET &PREFIX &CALLED &API_RUN &SUFFIX).
  destruct(gateway_actual_none_api_run backend ge python objects detached io stable thread_errno heap_allocation decimal_float
    leases runtime references roots object_threads(Vptr none_symbol Ptrofs.zero)(gateway_value_environment slots)
    called called_world reference result returned returned_world CONSTANTS
    (gateway_value_active_environment native stable base slots stream_block stream_offset final_stream readonly original
      called called_world(proj1 CALLED))API_RUN)
    as(ticket &HELD &RETURN_ENV).
  set(captured:={|gateway_held_ticket:=ticket;gateway_held_object:=Vptr none_symbol Ptrofs.zero;
    gateway_held_view:=gateway_held_scalar_value gateway_none_object|}).
  pose proof(gateway_thread_with_held_values backend io native stable base thread_errno heap_allocation
    python objects decimal_float leases roots[captured]runtime object_threads)as HELD_RUNTIME.
  assert(READY:gateway_return_environment native
    (gateway_held_discipline base python objects decimal_float leases[captured])None
    (gateway_value_environment slots)returned returned_world).
  { split;[split;[exact(proj1 RETURN_ENV)|exact HELD]|exact(proj2 RETURN_ENV)]. }
  destruct(gateway_actual_caller_return_side backend ge io native stable _ thread_errno HELD_RUNTIME
    None f_host_value None(gateway_value_environment slots)(gateway_value_none_parameters arguments initial)
    (match gateway_value_none_return with Sreturn expression=>expression|_=>None end)
    (Kseq gateway_value_after_null Kstop)returned returned_world suffix result value after next
    eq_refl READY SUFFIX)as[[AFTER_READY AFTER_HELD]SUFFIX_QUIET].
  assert(EMPTY:gateway_received_bytes io descriptor events=[]).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io descriptor prefix QUIET),
      (gateway_object_run_no_direct_receive backend ge io gateway_api_incref python_incref_definition
        [Vptr none_symbol Ptrofs.zero]called called_world reference result returned returned_world descriptor
        projection eq_refl API_RUN),(gateway_quiet_received io descriptor suffix SUFFIX_QUIET);reflexivity. }
  exists ticket;split;[exact VALUE|].
  rewrite VALUE;split;[exact AFTER_HELD|]. split.
  - apply gateway_heap_null.
    destruct(Forall_inv AFTER_HELD)as[LEASE[ROOT[PRIVATE[DESTRUCTIBLE[LOOKUP CHILDREN]]]]];exact LOOKUP.
  - split;[exact AFTER_READY|exact EMPTY].
Qed.

End NullHeap.
