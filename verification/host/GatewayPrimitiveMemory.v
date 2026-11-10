(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Primitive decoder branches retain disjoint stream and caller storage. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayObjectConstants GatewayObjectDiscipline GatewayPrimitiveValues GatewayPrimitiveBindings GatewayBindings
  GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueTag GatewayValueRegions GatewayValueNull
  GatewayValueNullSource GatewayValueBoolean GatewayValueBooleanCut GatewayValueReturns GatewayValueEnvironment
  GatewayNativeRegions GatewayScopedMemory GatewayReturnMemory GatewayScalarMemory GatewayNoneMemory
  GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.

Section PrimitiveMemory.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects).

Theorem gateway_actual_primitive_branch_memory primitive slots arguments initial stream_block stream_offset final_stream
    readonly original protected before world events value after next none_symbol :
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero) ->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol ->
  gateway_value_tagged native stable base slots stream_block stream_offset final_stream readonly original
    (Int64.repr(gateway_primitive_tag primitive))before world ->
  gateway_native_region_owned native protected before world ->
  gateway_environment_avoids protected(gateway_value_environment slots) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_native_region_context native base None protected before after next.
Proof.
  intros CONSTANTS NONE INPUT OWNED AVOIDS RUN NONNULL.
  set(property:=fun memory current=>gateway_value_tagged native stable base slots stream_block stream_offset final_stream
    readonly original(Int64.repr(gateway_primitive_tag primitive))memory current /\
    gateway_return_region_context native base None(gateway_value_environment slots)protected before memory current).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros first current last following[TAGGED REGION]INTERFERENCE;split.
    - eapply gateway_value_tagged_ambient;[exact runtime|exact TAGGED|exact INTERFERENCE].
    - eapply gateway_return_region_ambient;[exact runtime|exact REGION|exact INTERFERENCE]. }
  assert(GOOD:property before world).
  { split;[exact INPUT|]. split.
    - exact(gateway_value_active_environment native stable base slots stream_block stream_offset final_stream readonly original
        before world(proj1 INPUT)).
    - split;[exact OWNED|apply Mem.unchanged_on_refl]. }
  destruct primitive as[|flag].
  - destruct actual_gateway_incref_binding as[reference_symbol[REFERENCE FUNCTION]].
    destruct(gateway_actual_null_reference backend(Clight.globalenv prog)property slots arguments initial before world
      events value after next none_symbol reference_symbol python_incref_definition CLOSED
      ltac:(intros;exact(proj2(proj1 H)))NONE REFERENCE FUNCTION eq_refl GOOD RUN)
      as(prefix &reference &suffix &called &called_world &result &returned &returned_world &
        EVENTS &VALUE &QUIET &PREFIX &CALLED &API_RUN &SUFFIX).
    pose proof(gateway_actual_none_api_memory backend(Clight.globalenv prog)python objects detached io stable thread_errno
      runtime references(Vptr none_symbol Ptrofs.zero)(gateway_value_environment slots)protected before
      called called_world reference result returned returned_world CONSTANTS(proj2 CALLED)API_RUN)as RETURN_ENV.
    exact(gateway_actual_caller_return_memory backend(Clight.globalenv prog)io native stable base thread_errno runtime
      None f_host_value None(gateway_value_environment slots)(gateway_value_none_parameters arguments initial)
      (match gateway_value_none_return with Sreturn expression=>expression|_=>None end)
      (Kseq gateway_value_after_null Kstop)protected before returned returned_world suffix result value after next
      eq_refl AVOIDS RETURN_ENV SUFFIX).
  - destruct actual_gateway_boolean_binding as[definition[DEFINITION[[symbol[SYMBOL FUNCTION]]TYPE]]].
    assert(LOADED:forall memory current,property memory current ->Mem.loadv Mint64 memory
      (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(gateway_value_boolean_tag flag))).
    { intros memory current[TAGGED REST];destruct flag;exact(proj2 TAGGED). }
    destruct(gateway_actual_boolean_call backend(Clight.globalenv prog)property flag slots arguments initial before world
      events value after next symbol definition CLOSED LOADED SYMBOL FUNCTION TYPE GOOD RUN)
      as(prefix &reference &suffix &called &called_world &result &returned &returned_world &
        EVENTS &QUIET &PREFIX &CALLED &API_RUN &SUFFIX).
    assert(RESULT_NONNULL:result<>Vnullptr).
    { intro NULL;subst result;apply NONNULL.
      exact(gateway_value_boolean_returned backend(Clight.globalenv prog)flag slots arguments initial returned returned_world
        suffix Vnullptr value after next(or_introl eq_refl)SUFFIX). }
    pose proof(gateway_actual_scalar_api_memory backend(Clight.globalenv prog)python objects detached io stable thread_errno
      decimal_float runtime constructors gateway_api_bool definition[gateway_value_boolean_argument flag](gateway_bool_object flag)
      (gateway_value_environment slots)protected before property called called_world reference result returned returned_world
      DEFINITION CLOSED ltac:(intros;split;[constructor|exact I])CALLED(proj2 CALLED)API_RUN RESULT_NONNULL)as RETURN_ENV.
    exact(gateway_actual_caller_return_memory backend(Clight.globalenv prog)io native stable base thread_errno runtime
      None f_host_value(Some _t'3)(gateway_value_environment slots)(gateway_value_boolean_parameters flag arguments initial)
      (match gateway_value_boolean_return with Sreturn expression=>expression|_=>None end)
      (Kseq gateway_value_after_boolean Kstop)protected before returned returned_world suffix result value after next
      eq_refl AVOIDS RETURN_ENV SUFFIX).
Qed.

End PrimitiveMemory.
