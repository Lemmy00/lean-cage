(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual scalar return paths retain every older caller entry and
   bind the one new source result, including repeated-pointer aliases. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects
  GatewayReferences GatewayValue GatewayObjectDiscipline GatewayObjectConstants GatewayObjectThreads GatewayPrimitiveBindings
  GatewayPrimitiveValues GatewayPrimitiveMemory GatewayPrimitiveEncoding GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayValueActual GatewayValueRegions GatewayValueNodeMemory GatewayValueReturnContext GatewayValueBoolean GatewayNativeRegions GatewayRegionThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceActivation GatewayReferenceNull GatewayThreadInvariant GatewayStreamInterface GatewayThreadRuntime
  GatewayObjectEvents GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.

From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects
  GatewayReferences GatewayValue GatewayObjectDiscipline GatewayObjectConstants GatewayObjectThreads GatewayPrimitiveBindings
  GatewayPrimitiveValues GatewayPrimitiveMemory GatewayPrimitiveEncoding GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayValueActual GatewayValueRegions GatewayValueNodeMemory GatewayValueReturnContext GatewayValueBoolean GatewayNativeRegions GatewayRegionThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceActivation GatewayReferenceBoolean GatewayThreadInvariant GatewayStreamInterface GatewayThreadRuntime
  GatewayObjectEvents GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.

From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueActual
  GatewayValueNodeMemory GatewayValueTag GatewayScalarLength GatewayScalarContext GatewayScalarSize GatewayScalarBuffer GatewayScalarPayload
  GatewayScalarPayloadMemory GatewayScalarSizedFrames GatewayReferenceBytes GatewayValueStreamRelations GatewayScalarAllocationPath GatewayScalarReadPath GatewayScalarReadMemory
  GatewayNativeRegions GatewayRegionThreads GatewayRegionMemory GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayImport GatewayScalarEncoding GatewayWordValues GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceActivation GatewayReferenceAccounting GatewayReferenceThreads GatewayThreadInvariant.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueActual
  GatewayValueNodeMemory GatewayValueTag GatewayScalarLength GatewayScalarContext GatewayScalarSize GatewayScalarBuffer GatewayScalarPayload
  GatewayScalarPayloadMemory GatewayScalarSizedFrames GatewayReferenceText GatewayScalarDecoding GatewayValueStreamRelations GatewayScalarAllocationPath GatewayScalarReadPath GatewayScalarReadMemory
  GatewayNativeRegions GatewayRegionThreads GatewayRegionMemory GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayImport GatewayScalarEncoding GatewayWordValues GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceActivation GatewayReferenceAccounting GatewayReferenceThreads GatewayThreadInvariant.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

From HostGateway Require Import GatewayReferenceOwnedBoolean GatewayReferenceNormalForm GatewayReferenceStackBound.
Section OwnedNull.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop)
  (decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (projection:gateway_direct_io_projection backend io).

Theorem gateway_reference_actual_null_value_owned context ledger held byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_source_bound(Clight.globalenv prog)
    (Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)context before)ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero)->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol->
  Byte.unsigned byte=0->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world->
  (forall object position,readonly object position->native world object)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining->
  exists final final_stream,
    gateway_stream_read_after(gateway_stream_node_debit initial)1 final_stream /\
    gateway_value_context native stable base stream_block stream_offset final_stream readonly original after next /\
    (forall object position,readonly object position->native next object) /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))
      (gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_none_object)|}])next /\
    gateway_value_heap decimal_float(objects next)value
      LeanCage_Host_GatewayResponseCode_Value_null /\
    gateway_received_bytes io(stream_descriptor initial)events=[byte] /\
    gateway_reference_result_entries context ledger final(gateway_reference_next ledger)value /\
    gateway_reference_source_bound(Clight.globalenv prog)(Returnstate value context after)final.
Proof.
  intros CALL FORMED OLDER BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_fresh_call_places(Clight.globalenv prog)(Internal f_host_value)
    (gateway_value_arguments_list arguments)context before ledger BOUND)as[TEMPS RESULTS].
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation
    python objects decimal_float reference_threads ledger held runtime)as SCOPE_RUNTIME.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPE_RUNTIME readonly)as THREADS.
  assert(AUGMENTED_INPUT:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { pose proof INPUT as[SIDE CONTEXT];split.
    - split;[split;[exact SIDE|exact SCOPE]|].
      assert(ALL:gateway_native_region_owned native(gateway_value_input_region stream_block stream_offset readonly)before world)
        by(eapply gateway_value_return_native_region;[exact INPUT|exact READONLY]).
      intros object position POINT;exact(ALL object position(or_intror POINT)).
    - exact CONTEXT. }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno THREADS arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM AUGMENTED_INPUT RUN NONNULL)
    as(slots &selected &prefix &reading &suffix &word_before &word_world &word_after &word_next &final_stream &
      EVENTS &DEPTH &NODES &QUIET &PREFIX &ALLOCATED &READ &READ_BYTES &LOAD &STREAM_AFTER &ACTIVE &SUFFIX).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES
      in OBSERVED;inversion OBSERVED;reflexivity. }
  subst selected.
  rewrite TAG in LOAD.
  pose proof ACTIVE as[[[[SIDE SCOPE_AT_TAG]OWNED_READONLY]CONTEXT]STACK].
  assert(SCOPED_ACTIVE:gateway_value_active native stable scoped slots stream_block stream_offset final_stream readonly original
    word_after word_next).
  { split;[split;[split;[exact SIDE|exact SCOPE_AT_TAG]|exact CONTEXT]|exact STACK]. }
  destruct actual_gateway_incref_binding as[reference_symbol[REFERENCE FUNCTION]].
  destruct(gateway_reference_actual_null_branch backend(Clight.globalenv prog)python objects detached io stable thread_errno
    heap_allocation decimal_float runtime references reference_threads projection context ledger held slots arguments initial
    stream_block stream_offset final_stream readonly original word_after word_next suffix value after next none_symbol reference_symbol
    (stream_descriptor initial)CALL FORMED(RESULTS(gateway_reference_depth context))CONSTANTS NONE REFERENCE FUNCTION
    (conj SCOPED_ACTIVE LOAD)SUFFIX)
    as(final &RETURNED &WELL &OWNED &BINDING &HELD &VALUE &FINAL_SIDE &EMPTY &ORIGIN).
  assert(ENTRIES:gateway_reference_result_entries context ledger final(gateway_reference_next ledger)value).
  { exact(proj1(gateway_reference_mint_entries ledger final
      (gateway_reference_result(gateway_reference_depth context))value ORIGIN)). }
  assert(BASE_ACTIVE:gateway_value_active native stable base slots stream_block stream_offset final_stream readonly original word_after word_next).
  { split;[split;[exact SIDE|exact CONTEXT]|exact STACK]. }
  set(protected:=gateway_value_input_region stream_block stream_offset readonly).
  assert(OWNED_INPUT:gateway_native_region_owned native protected word_after word_next).
  { eapply gateway_value_return_native_region;[exact(proj1 BASE_ACTIVE)|].
    intros object position POINT;exact(proj2(OWNED_READONLY object position POINT)). }
  assert(MEMORY_INPUT:gateway_value_tagged native stable base slots stream_block stream_offset final_stream readonly original
    (Int64.repr(gateway_primitive_tag gateway_primitive_null))word_after word_next).
  { split;[exact BASE_ACTIVE|exact LOAD]. }
  pose proof(gateway_actual_primitive_branch_memory backend python objects detached io stable thread_errno decimal_float runtime
    constructors references gateway_primitive_null slots arguments initial stream_block stream_offset final_stream readonly original
    protected word_after word_next suffix value after next none_symbol CONSTANTS NONE MEMORY_INPUT OWNED_INPUT
    (gateway_value_environment_avoids_inputs native stable base slots stream_block stream_offset final_stream readonly original
      word_after word_next BASE_ACTIVE)SUFFIX NONNULL)as[MEMORY_SIDE[FINAL_OWNED FRAME]].
  assert(BYTES:gateway_received_bytes io(stream_descriptor initial)events=[byte]).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES,EMPTY;
      reflexivity. }
  exists final,final_stream;split;[exact STREAM_AFTER|]. split.
  - eapply gateway_value_context_return_frame;[exact runtime|exact(proj1 BASE_ACTIVE)|exact FINAL_SIDE|exact FINAL_OWNED|exact FRAME].
  - split;[intros object position POINT;exact(proj2(FINAL_OWNED object position(or_intror POINT)))|].
    split;[exact WELL|]. split;[exact OWNED|]. split;[exact BINDING|]. split;[exact HELD|].
    split;[exact VALUE|]. split;[exact BYTES|]. split;[exact ENTRIES|].
    eapply gateway_reference_result_entries_bound;[exact OLDER|exact ENTRIES].
Qed.

End OwnedNull.

Section OwnedBoolean.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop)
  (decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (projection:gateway_direct_io_projection backend io).

Theorem gateway_reference_actual_boolean_value_owned context ledger held(flag:bool)byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_source_bound(Clight.globalenv prog)
    (Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)context before)ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero)->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol->
  Byte.unsigned byte=(if flag then 2 else 1)->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world->
  (forall object position,readonly object position->native world object)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining->
  exists final final_stream,
    gateway_stream_read_after(gateway_stream_node_debit initial)1 final_stream /\
    gateway_value_context native stable base stream_block stream_offset final_stream readonly original after next /\
    (forall object position,readonly object position->native next object) /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))
      (gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_bool_object flag)|}])next /\
    gateway_value_heap decimal_float(objects next)value
      (LeanCage_Host_GatewayResponseCode_Value_boolean(if flag then Bool_true else Bool_false)) /\
    gateway_received_bytes io(stream_descriptor initial)events=[byte] /\
    gateway_reference_result_entries context ledger final(gateway_reference_next ledger)value /\
    gateway_reference_source_bound(Clight.globalenv prog)(Returnstate value context after)final.
Proof.
  intros CALL FORMED OLDER BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_fresh_call_places(Clight.globalenv prog)(Internal f_host_value)
    (gateway_value_arguments_list arguments)context before ledger BOUND)as[TEMPS RESULTS].
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation
    python objects decimal_float reference_threads ledger held runtime)as SCOPE_RUNTIME.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPE_RUNTIME readonly)as THREADS.
  assert(AUGMENTED_INPUT:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { pose proof INPUT as[SIDE CONTEXT];split.
    - split;[split;[exact SIDE|exact SCOPE]|].
      assert(ALL:gateway_native_region_owned native(gateway_value_input_region stream_block stream_offset readonly)before world)
        by(eapply gateway_value_return_native_region;[exact INPUT|exact READONLY]).
      intros object position POINT;exact(ALL object position(or_intror POINT)).
    - exact CONTEXT. }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno THREADS arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM AUGMENTED_INPUT RUN NONNULL)
    as(slots &selected &prefix &reading &suffix &word_before &word_world &word_after &word_next &final_stream &
      EVENTS &DEPTH &NODES &QUIET &PREFIX &ALLOCATED &READ &READ_BYTES &LOAD &STREAM_AFTER &ACTIVE &SUFFIX).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES
      in OBSERVED;inversion OBSERVED;reflexivity. }
  subst selected.
  assert(BOOL_TAG:Int64.repr(Byte.unsigned byte)=gateway_value_boolean_tag flag).
  { rewrite TAG;destruct flag;reflexivity. }
  rewrite BOOL_TAG in LOAD.
  pose proof ACTIVE as[[[[SIDE SCOPE_AT_TAG]OWNED_READONLY]CONTEXT]STACK].
  assert(SCOPED_ACTIVE:gateway_value_active native stable scoped slots stream_block stream_offset final_stream readonly original
    word_after word_next).
  { split;[split;[split;[exact SIDE|exact SCOPE_AT_TAG]|exact CONTEXT]|exact STACK]. }
  destruct actual_gateway_boolean_binding as[definition[DEFINITION[[symbol[SYMBOL FUNCTION]]TYPE]]].
  destruct(gateway_reference_actual_boolean_branch_owned backend(Clight.globalenv prog)python objects detached io stable thread_errno
    heap_allocation decimal_float runtime constructors reference_threads projection context ledger held flag slots arguments initial
    stream_block stream_offset final_stream readonly original word_after word_next suffix value after next symbol definition
    (stream_descriptor initial)CALL FORMED OLDER(RESULTS(S(gateway_reference_depth context)))
    (TEMPS _t'3(gateway_reference_depth context)(Nat.le_refl _))(RESULTS(gateway_reference_depth context))
    DEFINITION SYMBOL FUNCTION TYPE
    (conj SCOPED_ACTIVE LOAD)SUFFIX NONNULL)
    as(final &branch_prefix &constructing &tail &called &called_world &constructed &returned &returned_world &
      BRANCH_EVENTS &CONSTRUCTOR_RUN &RETURNED &WELL &OWNED &BINDING &HELD &VALUE &FINAL_SIDE &EMPTY &ORIGIN).
  destruct ORIGIN as[api_ledger[MINT[ANNOTATED ENTRIES]]].
  assert(BASE_ACTIVE:gateway_value_active native stable base slots stream_block stream_offset final_stream readonly original word_after word_next).
  { split;[split;[exact SIDE|exact CONTEXT]|exact STACK]. }
  set(protected:=gateway_value_input_region stream_block stream_offset readonly).
  assert(OWNED_INPUT:gateway_native_region_owned native protected word_after word_next).
  { eapply gateway_value_return_native_region;[exact(proj1 BASE_ACTIVE)|].
    intros object position POINT;exact(proj2(OWNED_READONLY object position POINT)). }
  assert(MEMORY_INPUT:gateway_value_tagged native stable base slots stream_block stream_offset final_stream readonly original
    (Int64.repr(gateway_primitive_tag(gateway_primitive_boolean flag)))word_after word_next).
  { split;[exact BASE_ACTIVE|]. destruct flag;exact LOAD. }
  pose proof(gateway_actual_primitive_branch_memory backend python objects detached io stable thread_errno decimal_float runtime
    constructors references(gateway_primitive_boolean flag)slots arguments initial stream_block stream_offset final_stream readonly original
    protected word_after word_next suffix value after next none_symbol CONSTANTS NONE MEMORY_INPUT OWNED_INPUT
    (gateway_value_environment_avoids_inputs native stable base slots stream_block stream_offset final_stream readonly original
      word_after word_next BASE_ACTIVE)SUFFIX NONNULL)as[MEMORY_SIDE[FINAL_OWNED FRAME]].
  assert(BYTES:gateway_received_bytes io(stream_descriptor initial)events=[byte]).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES,EMPTY;
      reflexivity. }
  exists final,final_stream;split;[exact STREAM_AFTER|]. split.
  - eapply gateway_value_context_return_frame;[exact runtime|exact(proj1 BASE_ACTIVE)|exact FINAL_SIDE|exact FINAL_OWNED|exact FRAME].
  - split;[intros object position POINT;exact(proj2(FINAL_OWNED object position(or_intror POINT)))|].
    split;[exact WELL|]. split;[exact OWNED|]. split;[exact BINDING|]. split;[exact HELD|].
    split;[exact VALUE|]. split;[exact BYTES|]. split;[exact ENTRIES|].
    eapply gateway_reference_result_entries_bound;[exact OLDER|exact ENTRIES].
Qed.

End OwnedBoolean.

Theorem gateway_reference_actual_bytes_stream_value_owned {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (errors:gateway_no_memory_runtime backend python)(io_projection:gateway_direct_io_projection backend io)
    context ledger held arguments before world events value after next stream_block stream_offset initial readonly original byte remaining :
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_source_bound(Clight.globalenv prog)
    (Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)context before)ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  Byte.unsigned byte=5 ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  exists final final_stream,
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    (gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset final_stream readonly original after next /\
      (forall candidate position,readonly candidate position ->gateway_native_private(python next)candidate)) /\
    exists size_bytes payload,
    length size_bytes=8%nat /\gateway_decoded_value size_bytes=Z.of_nat(length payload) /\
    gateway_received_bytes io(stream_descriptor initial)events=byte::(size_bytes++payload) /\
    gateway_scalar_stream_after initial 8(Z.of_nat(length payload))final_stream /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_bytes_object payload)|}])next /\
    gateway_value_heap decimal_float(objects next)value(gateway_wire_scalar 5 payload) /\
    gateway_reference_result_entries context ledger final(gateway_reference_next ledger)value /\
    gateway_reference_source_bound(Clight.globalenv prog)(Returnstate value context after)final.
Proof.
  intros CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  destruct(gateway_reference_fresh_call_places(Clight.globalenv prog)(Internal f_host_value)
    (gateway_value_arguments_list arguments)context before ledger BOUND)as[TEMPS RESULTS].
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    reference_threads ledger held runtime)as SCOPED_RUNTIME.
  pose proof(gateway_memory_with_reference_scope backend io native stable base heap_allocation python objects decimal_float
    reference_threads ledger held allocations)as SCOPED_MEMORY.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPED_RUNTIME readonly)as THREADS.
  pose proof(gateway_memory_with_native_region backend io native stable scoped heap_allocation SCOPED_MEMORY readonly)as MEMORY.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { destruct INPUT as[SIDE[PRIVATE[STABLE[RAW FRAME]]]].
    intros candidate position READ;split;
      [exact(gateway_value_readonly_live _ _ _ _ _ RAW candidate position READ)|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED_INPUT:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { destruct INPUT as[SIDE REST];split;[split;[split;[exact SIDE|exact SCOPE]|exact OWNED]|exact REST]. }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno THREADS arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM AUGMENTED_INPUT RUN NONNULL)
    as(slots &selected &tag_prefix &tag_read &tag_suffix &tag_before &tag_world &tag_after &tag_next &tag_stream &
      EVENTS &DEPTH &NODES &TAG_QUIET &TAG_PREFIX &ALLOCATED &TAG_RUN &TAG_OBSERVED &TAG_LOAD &TAG_STREAM &TAG_ACTIVE &TAG_REST).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),TAG_OBSERVED in OBSERVED.
    inversion OBSERVED;reflexivity. }
  subst selected;rewrite TAG in TAG_LOAD.
  destruct(gateway_actual_scalar_size backend io native stable augmented thread_errno THREADS gateway_scalar_bytes slots arguments initial
    stream_block stream_offset tag_stream readonly original tag_after tag_next tag_suffix value after next STREAM(conj TAG_ACTIVE TAG_LOAD)TAG_REST NONNULL)
    as(size_parameters &size_bytes &size_prefix &size_read &size_suffix &size_before &size_world &size_after &size_next &size_stream &
      SIZE_EVENTS &SIZE_QUIET &SIZE_PARAMETER &SIZE_DEPTH &SIZE_PREFIX &SIZE_RUN &SIZE_OBSERVED &SIZE_COUNT &SIZE_LOAD &SIZE_STREAM &SIZE_ACTIVE &SIZE_REST).
  set(size:=Int64.repr(gateway_decoded_value size_bytes)).
  assert(SIZE_WIDTH:length size_bytes=8%nat)by(change(Z.of_nat(length size_bytes)=8)in SIZE_COUNT;lia).
  destruct(gateway_actual_scalar_buffer_context backend python objects detached io native stable thread_errno heap_allocation augmented runtime THREADS MEMORY errors
    gateway_scalar_bytes slots arguments size_parameters stream_block stream_offset size_stream readonly original size size_after size_next size_suffix value after next
    ltac:(intros memory current[[SIDE HELD]PROTECTED];exact SIDE)STREAM SIZE_PARAMETER(conj SIZE_ACTIVE SIZE_LOAD)SIZE_REST NONNULL)
    as(MAXIMUM &object &malloc_parameters &allocation_prefix &allocating &allocation_suffix &malloc_before &malloc_world &malloc_after &malloc_next &
      ALLOCATION_EVENTS &ALLOCATION_QUIET &MALLOC_PARAMETER &MALLOC_RUN &MALLOC_READY &ALLOCATION_EMPTY &ALLOCATION_REST).
  destruct(gateway_actual_scalar_payload backend io native stable augmented thread_errno THREADS heap_allocation gateway_scalar_bytes slots arguments
    malloc_parameters stream_block stream_offset size_stream readonly original size object malloc_after malloc_next allocation_suffix value after next
    STREAM MALLOC_PARAMETER MALLOC_READY ALLOCATION_REST NONNULL)
    as(read_parameters &payload_prefix &payload_read &payload_suffix &payload_before &payload_world &payload_after &payload_next &payload &payload_stream &
      PAYLOAD_EVENTS &PAYLOAD_QUIET &READ_STREAM &READ_BUFFER &READ_RUN &RECEIPT &PAYLOAD_STREAM &PAYLOAD_READY &PAYLOAD_REST).
  pose proof PAYLOAD_READY as[_[[[PAYLOAD_SIDE PAYLOAD_OWNED]HEAP]SEPARATE]].
  pose proof RECEIPT as[PAYLOAD_COUNT PAYLOAD_FITS PAYLOAD_OBSERVED PAYLOAD_LOAD DATA_PERMISSIONS STREAM_PERMISSIONS FINAL_STREAM READ_FRAME].
  assert(BASE_READY:gateway_scalar_payload_ready native stable base heap_allocation gateway_scalar_bytes slots stream_block stream_offset payload_stream readonly original
    size object payload payload_after payload_next).
  { split;[eapply gateway_scalar_buffer_rebase;[exact PAYLOAD_READY|exact(proj1 PAYLOAD_SIDE)]|].
    split;[exact PAYLOAD_COUNT|exact PAYLOAD_LOAD]. }
  destruct(gateway_reference_actual_bytes_value backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations constructors reference_threads io_projection context ledger held slots read_parameters stream_block stream_offset
    payload_stream readonly original size object payload payload_after payload_next payload_suffix value after next
    FORMED(RESULTS(gateway_reference_depth context))(proj2 PAYLOAD_SIDE)READ_BUFFER MAXIMUM BASE_READY
    ltac:(intros candidate position READ;exact(proj2(PAYLOAD_OWNED candidate position READ)))PAYLOAD_REST NONNULL)
    as(final &WELL &ROOT &ROOT_BINDING &HELD &FINAL &FINAL_NATIVE &HEAP_VALUE &FINAL_EMPTY &MINT).
  assert(ENTRIES:gateway_reference_result_entries context ledger final(gateway_reference_next ledger)value).
  { exact(proj1(gateway_reference_mint_entries ledger final
      (gateway_reference_result(gateway_reference_depth context))value MINT)). }
  assert(TAG_DESCRIPTOR:stream_descriptor tag_stream=stream_descriptor initial)by(exact(proj1 TAG_STREAM)).
  assert(SIZE_DESCRIPTOR:stream_descriptor size_stream=stream_descriptor initial).
  { rewrite(proj1 SIZE_STREAM);exact TAG_DESCRIPTOR. }
  assert(PAYLOAD_DESCRIPTOR:stream_descriptor payload_stream=stream_descriptor initial).
  { rewrite(proj1 PAYLOAD_STREAM);exact SIZE_DESCRIPTOR. }
  assert(SIZE_VALUE:gateway_decoded_value size_bytes=Z.of_nat(length payload)).
  { pose proof PAYLOAD_COUNT as COUNT.
    unfold size in COUNT;rewrite gateway_decoded_unsigned in COUNT by lia;lia. }
  assert(EXACT_BYTES:gateway_received_bytes io(stream_descriptor initial)events=byte::(size_bytes++payload)).
  { rewrite EVENTS,SIZE_EVENTS,ALLOCATION_EVENTS,PAYLOAD_EVENTS,!gateway_received_append,
      (gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),TAG_OBSERVED,
      (gateway_quiet_received io(stream_descriptor initial)size_prefix SIZE_QUIET),
      <-TAG_DESCRIPTOR,SIZE_OBSERVED,TAG_DESCRIPTOR,
      (gateway_quiet_received io(stream_descriptor initial)allocation_prefix ALLOCATION_QUIET),
      <-SIZE_DESCRIPTOR,ALLOCATION_EMPTY,SIZE_DESCRIPTOR,
      (gateway_quiet_received io(stream_descriptor initial)payload_prefix PAYLOAD_QUIET),
      <-SIZE_DESCRIPTOR,PAYLOAD_OBSERVED,SIZE_DESCRIPTOR,
      <-PAYLOAD_DESCRIPTOR,FINAL_EMPTY;cbn;repeat rewrite app_nil_r;reflexivity. }
  exists final,payload_stream;split;[exact WELL|]. split;[exact ROOT|]. split;[exact ROOT_BINDING|].
  split;[split;[exact FINAL|exact FINAL_NATIVE]|]. exists size_bytes,payload.
  split;[exact SIZE_WIDTH|]. split;[exact SIZE_VALUE|]. split;[exact EXACT_BYTES|]. split.
  - exists tag_stream,size_stream;split;[exact TAG_STREAM|]. split;[exact SIZE_STREAM|]. rewrite PAYLOAD_COUNT;exact PAYLOAD_STREAM.
  - split;[exact HELD|]. split;[exact HEAP_VALUE|]. split;[exact ENTRIES|].
    eapply gateway_reference_result_entries_bound;[exact OLDER|exact ENTRIES].
Qed.


Theorem gateway_reference_actual_text_stream_value_owned {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (errors:gateway_no_memory_runtime backend python)(io_projection:gateway_direct_io_projection backend io)
    context ledger held arguments before world events value after next stream_block stream_offset initial readonly original byte remaining mode_symbol :
  Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall candidate position,GatewayScalarDecoding.gateway_scalar_mode_region mode_symbol candidate position->readonly candidate position)->
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_source_bound(Clight.globalenv prog)
    (Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)context before)ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  Byte.unsigned byte=4 ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  exists final final_stream,
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    (gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset final_stream readonly original after next /\
      (forall candidate position,readonly candidate position ->gateway_native_private(python next)candidate)) /\
    exists size_bytes payload characters,
    length size_bytes=8%nat /\gateway_decoded_value size_bytes=Z.of_nat(length payload) /\
    gateway_received_bytes io(stream_descriptor initial)events=byte::(size_bytes++payload) /\
    gateway_scalar_stream_after initial 8(Z.of_nat(length payload))final_stream /\
    gateway_utf8_text payload characters /\gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_unicode_object characters)|}])next /\
    gateway_value_heap decimal_float(objects next)value(gateway_wire_scalar 4 payload) /\
    gateway_reference_result_entries context ledger final(gateway_reference_next ledger)value /\
    gateway_reference_source_bound(Clight.globalenv prog)(Returnstate value context after)final.
Proof.
  intros MODE_SYMBOL MODE SUBSET CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  destruct(gateway_reference_fresh_call_places(Clight.globalenv prog)(Internal f_host_value)
    (gateway_value_arguments_list arguments)context before ledger BOUND)as[TEMPS RESULTS].
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    reference_threads ledger held runtime)as SCOPED_RUNTIME.
  pose proof(gateway_memory_with_reference_scope backend io native stable base heap_allocation python objects decimal_float
    reference_threads ledger held allocations)as SCOPED_MEMORY.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPED_RUNTIME readonly)as THREADS.
  pose proof(gateway_memory_with_native_region backend io native stable scoped heap_allocation SCOPED_MEMORY readonly)as MEMORY.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { destruct INPUT as[SIDE[PRIVATE[STABLE[RAW FRAME]]]].
    intros candidate position READ;split;
      [exact(gateway_value_readonly_live _ _ _ _ _ RAW candidate position READ)|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED_INPUT:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { destruct INPUT as[SIDE REST];split;[split;[split;[exact SIDE|exact SCOPE]|exact OWNED]|exact REST]. }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno THREADS arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM AUGMENTED_INPUT RUN NONNULL)
    as(slots &selected &tag_prefix &tag_read &tag_suffix &tag_before &tag_world &tag_after &tag_next &tag_stream &
      EVENTS &DEPTH &NODES &TAG_QUIET &TAG_PREFIX &ALLOCATED &TAG_RUN &TAG_OBSERVED &TAG_LOAD &TAG_STREAM &TAG_ACTIVE &TAG_REST).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),TAG_OBSERVED in OBSERVED.
    inversion OBSERVED;reflexivity. }
  subst selected;rewrite TAG in TAG_LOAD.
  destruct(gateway_actual_scalar_size backend io native stable augmented thread_errno THREADS gateway_scalar_text slots arguments initial
    stream_block stream_offset tag_stream readonly original tag_after tag_next tag_suffix value after next STREAM(conj TAG_ACTIVE TAG_LOAD)TAG_REST NONNULL)
    as(size_parameters &size_bytes &size_prefix &size_read &size_suffix &size_before &size_world &size_after &size_next &size_stream &
      SIZE_EVENTS &SIZE_QUIET &SIZE_PARAMETER &SIZE_DEPTH &SIZE_PREFIX &SIZE_RUN &SIZE_OBSERVED &SIZE_COUNT &SIZE_LOAD &SIZE_STREAM &SIZE_ACTIVE &SIZE_REST).
  set(size:=Int64.repr(gateway_decoded_value size_bytes)).
  assert(SIZE_WIDTH:length size_bytes=8%nat)by(change(Z.of_nat(length size_bytes)=8)in SIZE_COUNT;lia).
  destruct(gateway_actual_scalar_buffer_context backend python objects detached io native stable thread_errno heap_allocation augmented runtime THREADS MEMORY errors
    gateway_scalar_text slots arguments size_parameters stream_block stream_offset size_stream readonly original size size_after size_next size_suffix value after next
    ltac:(intros memory current[[SIDE HELD]PROTECTED];exact SIDE)STREAM SIZE_PARAMETER(conj SIZE_ACTIVE SIZE_LOAD)SIZE_REST NONNULL)
    as(MAXIMUM &object &malloc_parameters &allocation_prefix &allocating &allocation_suffix &malloc_before &malloc_world &malloc_after &malloc_next &
      ALLOCATION_EVENTS &ALLOCATION_QUIET &MALLOC_PARAMETER &MALLOC_RUN &MALLOC_READY &ALLOCATION_EMPTY &ALLOCATION_REST).
  destruct(gateway_actual_scalar_payload backend io native stable augmented thread_errno THREADS heap_allocation gateway_scalar_text slots arguments
    malloc_parameters stream_block stream_offset size_stream readonly original size object malloc_after malloc_next allocation_suffix value after next
    STREAM MALLOC_PARAMETER MALLOC_READY ALLOCATION_REST NONNULL)
    as(read_parameters &payload_prefix &payload_read &payload_suffix &payload_before &payload_world &payload_after &payload_next &payload &payload_stream &
      PAYLOAD_EVENTS &PAYLOAD_QUIET &READ_STREAM &READ_BUFFER &READ_RUN &RECEIPT &PAYLOAD_STREAM &PAYLOAD_READY &PAYLOAD_REST).
  pose proof PAYLOAD_READY as[_[[[PAYLOAD_SIDE PAYLOAD_OWNED]HEAP]SEPARATE]].
  pose proof RECEIPT as[PAYLOAD_COUNT PAYLOAD_FITS PAYLOAD_OBSERVED PAYLOAD_LOAD DATA_PERMISSIONS STREAM_PERMISSIONS FINAL_STREAM READ_FRAME].
  assert(BASE_READY:gateway_scalar_payload_ready native stable base heap_allocation gateway_scalar_text slots stream_block stream_offset payload_stream readonly original
    size object payload payload_after payload_next).
  { split;[eapply gateway_scalar_buffer_rebase;[exact PAYLOAD_READY|exact(proj1 PAYLOAD_SIDE)]|].
    split;[exact PAYLOAD_COUNT|exact PAYLOAD_LOAD]. }
  destruct(gateway_reference_actual_text_value backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations constructors reference_threads io_projection context ledger held slots read_parameters stream_block stream_offset
    payload_stream readonly original size object payload payload_after payload_next payload_suffix value after next mode_symbol MODE_SYMBOL MODE SUBSET
    FORMED(RESULTS(gateway_reference_depth context))(proj2 PAYLOAD_SIDE)READ_BUFFER MAXIMUM BASE_READY
    ltac:(intros candidate position READ;exact(proj2(PAYLOAD_OWNED candidate position READ)))PAYLOAD_REST NONNULL)
    as(final &characters &DECODED &WELL &ROOT &ROOT_BINDING &HELD &FINAL &FINAL_NATIVE &HEAP_VALUE &FINAL_EMPTY &MINT).
  assert(ENTRIES:gateway_reference_result_entries context ledger final(gateway_reference_next ledger)value).
  { exact(proj1(gateway_reference_mint_entries ledger final
      (gateway_reference_result(gateway_reference_depth context))value MINT)). }
  assert(TAG_DESCRIPTOR:stream_descriptor tag_stream=stream_descriptor initial)by(exact(proj1 TAG_STREAM)).
  assert(SIZE_DESCRIPTOR:stream_descriptor size_stream=stream_descriptor initial).
  { rewrite(proj1 SIZE_STREAM);exact TAG_DESCRIPTOR. }
  assert(PAYLOAD_DESCRIPTOR:stream_descriptor payload_stream=stream_descriptor initial).
  { rewrite(proj1 PAYLOAD_STREAM);exact SIZE_DESCRIPTOR. }
  assert(SIZE_VALUE:gateway_decoded_value size_bytes=Z.of_nat(length payload)).
  { pose proof PAYLOAD_COUNT as COUNT.
    unfold size in COUNT;rewrite gateway_decoded_unsigned in COUNT by lia;lia. }
  assert(EXACT_BYTES:gateway_received_bytes io(stream_descriptor initial)events=byte::(size_bytes++payload)).
  { rewrite EVENTS,SIZE_EVENTS,ALLOCATION_EVENTS,PAYLOAD_EVENTS,!gateway_received_append,
      (gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),TAG_OBSERVED,
      (gateway_quiet_received io(stream_descriptor initial)size_prefix SIZE_QUIET),
      <-TAG_DESCRIPTOR,SIZE_OBSERVED,TAG_DESCRIPTOR,
      (gateway_quiet_received io(stream_descriptor initial)allocation_prefix ALLOCATION_QUIET),
      <-SIZE_DESCRIPTOR,ALLOCATION_EMPTY,SIZE_DESCRIPTOR,
      (gateway_quiet_received io(stream_descriptor initial)payload_prefix PAYLOAD_QUIET),
      <-SIZE_DESCRIPTOR,PAYLOAD_OBSERVED,SIZE_DESCRIPTOR,
      <-PAYLOAD_DESCRIPTOR,FINAL_EMPTY;cbn;repeat rewrite app_nil_r;reflexivity. }
  exists final,payload_stream;split;[exact WELL|]. split;[exact ROOT|]. split;[exact ROOT_BINDING|].
  split;[split;[exact FINAL|exact FINAL_NATIVE]|]. exists size_bytes,payload,characters.
  split;[exact SIZE_WIDTH|]. split;[exact SIZE_VALUE|]. split;[exact EXACT_BYTES|]. split.
  - exists tag_stream,size_stream;split;[exact TAG_STREAM|]. split;[exact SIZE_STREAM|]. rewrite PAYLOAD_COUNT;exact PAYLOAD_STREAM.
  - split;[exact DECODED|]. split;[exact HELD|]. split;[exact HEAP_VALUE|]. split;[exact ENTRIES|].
    eapply gateway_reference_result_entries_bound;[exact OLDER|exact ENTRIES].
Qed.