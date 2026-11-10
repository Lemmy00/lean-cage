(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual scalar source calls produce the recursive graph/framing receipt
   used by their enclosing containers and the public response consumer. *)
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
From HostGateway Require Import GatewayReferenceOwnedValues GatewayReferenceOwnedPath GatewayReferenceDecoded GatewayReferenceParseResult GatewayContainerEncoding GatewayPrimitiveEncoding GatewayScalarEncoding GatewayValueStreamRelations.
Section ParseNull.
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


Theorem gateway_reference_parse_null context ledger held byte remaining arguments before world events value after next
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
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros CALL FORMED OLDER BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_actual_null_value_owned backend python objects detached io stable thread_errno heap_allocation decimal_float
    runtime constructors references reference_threads projection context ledger held byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol CALL FORMED OLDER BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED)
    as(final &final_stream &READ &FINAL_CONTEXT &FINAL_NATIVE &WELL &OWNER &BINDING &HELD &VALUE &BYTES &ENTRIES &FINAL_BOUND).
  exists final,final_stream,(LeanCage_Host_GatewayResponseCode_Value_null),(gateway_reference_next ledger).
  split.
  - eapply gateway_reference_leaf_receipt with(captured:={|gateway_held_ticket:=gateway_reference_next ledger;
      gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_none_object)|});
      [exact WELL|exact ENTRIES|apply Nat.le_refl|exact FINAL_BOUND|exact OWNER|exact HELD|reflexivity|reflexivity|exact VALUE|constructor].
  - split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;[exact(proj1 READ)|]. constructor;rewrite BYTES.
    apply gateway_null_source_encoding;exact TAG.
Qed.
End ParseNull.

Section ParseBoolean.
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


Theorem gateway_reference_parse_boolean context ledger held(flag:bool)byte remaining arguments before world events value after next
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
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros CALL FORMED OLDER BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_actual_boolean_value_owned backend python objects detached io stable thread_errno heap_allocation decimal_float
    runtime constructors references reference_threads projection context ledger held flag byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol CALL FORMED OLDER BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED)
    as(final &final_stream &READ &FINAL_CONTEXT &FINAL_NATIVE &WELL &OWNER &BINDING &HELD &VALUE &BYTES &ENTRIES &FINAL_BOUND).
  exists final,final_stream,(LeanCage_Host_GatewayResponseCode_Value_boolean(if flag then Bool_true else Bool_false)),(gateway_reference_next ledger).
  split.
  - eapply gateway_reference_leaf_receipt with(captured:={|gateway_held_ticket:=gateway_reference_next ledger;
      gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_bool_object flag)|});
      [exact WELL|exact ENTRIES|apply Nat.le_refl|exact FINAL_BOUND|exact OWNER|exact HELD|reflexivity|reflexivity|exact VALUE|constructor].
  - split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;[exact(proj1 READ)|]. constructor;rewrite BYTES.
    apply gateway_boolean_source_encoding;exact TAG.
Qed.
End ParseBoolean.

Theorem gateway_reference_parse_bytes {World Event}(backend:gateway_backend World Event)
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
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_actual_bytes_stream_value_owned backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations constructors reference_threads errors io_projection context ledger held arguments before world events value after next stream_block stream_offset initial readonly original byte remaining CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED)
    as(final &final_stream &WELL &OWNER &BINDING &[FINAL_CONTEXT FINAL_NATIVE] &size_bytes &payload &
      WIDTH &COUNT &BYTES &STREAM_AFTER &HELD &VALUE &ENTRIES &FINAL_BOUND).
  exists final,final_stream,(gateway_wire_scalar 5 payload),(gateway_reference_next ledger).
  split.
  - eapply gateway_reference_leaf_receipt with(captured:={|gateway_held_ticket:=gateway_reference_next ledger;
      gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_bytes_object payload)|});
      [exact WELL|exact ENTRIES|apply Nat.le_refl|exact FINAL_BOUND|exact OWNER|exact HELD|reflexivity|reflexivity|exact VALUE|constructor].
  - split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;
      [eapply gateway_scalar_stream_descriptor;exact STREAM_AFTER|]. constructor;rewrite BYTES.
    exact(gateway_scalar_source_encoding gateway_scalar_bytes byte size_bytes payload TAG WIDTH COUNT).
Qed.

Theorem gateway_reference_parse_text {World Event}(backend:gateway_backend World Event)
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
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros MODE_SYMBOL MODE SUBSET CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_actual_text_stream_value_owned backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations constructors reference_threads errors io_projection context ledger held arguments before world events value after next stream_block stream_offset initial readonly original byte remaining mode_symbol MODE_SYMBOL MODE SUBSET CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED)
    as(final &final_stream &WELL &OWNER &BINDING &[FINAL_CONTEXT FINAL_NATIVE] &size_bytes &payload &characters &
      WIDTH &COUNT &BYTES &STREAM_AFTER &DECODED &HELD &VALUE &ENTRIES &FINAL_BOUND).
  exists final,final_stream,(gateway_wire_scalar 4 payload),(gateway_reference_next ledger).
  split.
  - eapply gateway_reference_leaf_receipt with(captured:={|gateway_held_ticket:=gateway_reference_next ledger;
      gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_unicode_object characters)|});
      [exact WELL|exact ENTRIES|apply Nat.le_refl|exact FINAL_BOUND|exact OWNER|exact HELD|reflexivity|reflexivity|exact VALUE|constructor].
  - split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;
      [eapply gateway_scalar_stream_descriptor;exact STREAM_AFTER|]. constructor;rewrite BYTES.
    exact(gateway_scalar_source_encoding gateway_scalar_text byte size_bytes payload TAG WIDTH COUNT).
Qed.

Theorem gateway_reference_parse_path {World Event}(backend:gateway_backend World Event)
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
  Byte.unsigned byte=6 ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_actual_path_stream_value_owned backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations constructors reference_threads errors io_projection context ledger held arguments before world events value after next stream_block stream_offset initial readonly original byte remaining CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED)
    as(final &final_stream &WELL &OWNER &BINDING &[FINAL_CONTEXT FINAL_NATIVE] &size_bytes &payload &characters &
      WIDTH &COUNT &BYTES &STREAM_AFTER &DECODED &HELD &VALUE &ENTRIES &FINAL_BOUND).
  exists final,final_stream,(gateway_wire_scalar 6 payload),(gateway_reference_next ledger).
  split.
  - eapply gateway_reference_leaf_receipt with(captured:={|gateway_held_ticket:=gateway_reference_next ledger;
      gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_unicode_object characters)|});
      [exact WELL|exact ENTRIES|apply Nat.le_refl|exact FINAL_BOUND|exact OWNER|exact HELD|reflexivity|reflexivity|exact VALUE|constructor].
  - split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;
      [eapply gateway_scalar_stream_descriptor;exact STREAM_AFTER|]. constructor;rewrite BYTES.
    exact(gateway_scalar_source_encoding gateway_scalar_path byte size_bytes payload TAG WIDTH COUNT).
Qed.
