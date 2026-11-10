(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual Boolean dispatch returns the constructed builtin with its own lease. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayRootLeases GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayScalarRuns
  GatewayValueEntry GatewayValueStack GatewayValueTag GatewayValueBoolean GatewayValueReturns GatewayValueRegions
  GatewayValueEnvironment GatewayValueBooleanCut GatewayReturnRuntime GatewayCallerReturns GatewayObjectRuns
  GatewayObjectEvents GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section BooleanHeap.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->BinNums.Z->Prop)
  (decimal_float:list BinNums.Z->Floats.float->Prop)(leases:World->nat->Values.val->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
  (object_threads:gateway_object_thread_contract backend native stable base heap_allocation python objects leases)
  (projection:gateway_direct_io_projection backend io).

Theorem gateway_actual_boolean_branch flag slots arguments initial stream_block stream_offset final_stream readonly original
    before world events value after next symbol definition descriptor :
  gateway_object_api_definition gateway_api_bool=Some definition ->
  Genv.find_symbol ge _PyBool_FromLong=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tlong](tptr(Tstruct __object noattr))cc_default ->
  gateway_value_tagged native stable base slots stream_block stream_offset final_stream readonly original
    (gateway_value_boolean_tag flag)before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists ticket,gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_bool_object flag)|}]next /\
    gateway_value_heap decimal_float(objects next)value
      (LeanCage_Host_GatewayResponseCode_Value_boolean(if flag then Bool_true else Bool_false)) /\
    base None after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros DEFINITION SYMBOL FUNCTION TYPE INPUT RUN NONNULL.
  set(property:=gateway_value_tagged native stable base slots stream_block stream_offset final_stream readonly original
    (gateway_value_boolean_tag flag)).
  pose proof(gateway_value_tagged_ambient backend io native stable base thread_errno runtime
    slots stream_block stream_offset final_stream readonly original(gateway_value_boolean_tag flag))as CLOSED.
  destruct(gateway_actual_boolean_call backend ge property flag slots arguments initial before world events value after next
    symbol definition CLOSED ltac:(intros;exact(proj2 H))SYMBOL FUNCTION TYPE INPUT RUN)
    as(prefix &reference &suffix &called &called_world &result &returned &returned_world &
      EVENTS &QUIET &PREFIX &CALLED &API_RUN &SUFFIX).
  assert(RESULT_NONNULL:result<>Vnullptr).
  { intro NULL;subst result;apply NONNULL.
    exact(gateway_value_boolean_returned backend ge flag slots arguments initial returned returned_world suffix
      Vnullptr value after next(or_introl eq_refl)SUFFIX). }
  destruct(gateway_actual_scalar_api_run backend ge python objects detached io stable thread_errno heap_allocation decimal_float
    leases runtime constructors roots object_threads gateway_api_bool definition[gateway_value_boolean_argument flag]
    (gateway_bool_object flag)gateway_bool_kind(gateway_value_environment slots)property
    called called_world reference result returned returned_world DEFINITION CLOSED
    ltac:(intros;split;[constructor|exact I])eq_refl eq_refl ltac:(right;left;reflexivity)
    CALLED(gateway_value_active_environment native stable base slots stream_block stream_offset final_stream readonly original
      called called_world(proj1 CALLED))API_RUN RESULT_NONNULL)
    as(ticket &HELD &RETURN_ENV).
  assert(POINTER:gateway_object_pointer_value result).
  { destruct(Forall_inv HELD)as[LEASE[ROOT REST]].
    destruct(proj1(proj1 RETURN_ENV))as[VALID[LIVE[BYTES[DICTIONARY POINTER]]]].
    destruct(POINTER result ROOT)as[object[offset[EQUAL VALID_POINTER]]];right;eauto. }
  pose proof(gateway_value_boolean_returned backend ge flag slots arguments initial returned returned_world suffix
    result value after next POINTER SUFFIX)as VALUE.
  set(captured:={|gateway_held_ticket:=ticket;gateway_held_object:=result;
    gateway_held_view:=gateway_held_scalar_value(gateway_bool_object flag)|}).
  pose proof(gateway_thread_with_held_values backend io native stable base thread_errno heap_allocation
    python objects decimal_float leases roots[captured]runtime object_threads)as HELD_RUNTIME.
  assert(READY:gateway_return_environment native
    (gateway_held_discipline base python objects decimal_float leases[captured])None
    (gateway_value_environment slots)returned returned_world).
  { split;[split;[exact(proj1 RETURN_ENV)|exact HELD]|exact(proj2 RETURN_ENV)]. }
  destruct(gateway_actual_caller_return_side backend ge io native stable _ thread_errno HELD_RUNTIME
    None f_host_value(Some _t'3)(gateway_value_environment slots)(gateway_value_boolean_parameters flag arguments initial)
    (match gateway_value_boolean_return with Sreturn expression=>expression|_=>None end)
    (Kseq gateway_value_after_boolean Kstop)returned returned_world suffix result value after next
    eq_refl READY SUFFIX)as[[AFTER_READY AFTER_HELD]SUFFIX_QUIET].
  assert(EMPTY:gateway_received_bytes io descriptor events=[]).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io descriptor prefix QUIET),
      (gateway_object_run_no_direct_receive backend ge io gateway_api_bool definition[gateway_value_boolean_argument flag]
        called called_world reference result returned returned_world descriptor projection DEFINITION API_RUN),
      (gateway_quiet_received io descriptor suffix SUFFIX_QUIET);reflexivity. }
  exists ticket;rewrite VALUE;split;[exact AFTER_HELD|]. split.
  - apply gateway_heap_boolean.
    destruct(Forall_inv AFTER_HELD)as[LEASE[ROOT[PRIVATE[DESTRUCTIBLE[LOOKUP CHILDREN]]]]];exact LOOKUP.
  - split;[exact AFTER_READY|exact EMPTY].
Qed.

End BooleanHeap.
