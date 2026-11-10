(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One aggregate source-count budget is retained through the
   same physical parser run, including pointer aliases with retained and retired holders. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayContainerEncoding GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectConstants GatewayObjectThreads GatewayObjectInstances GatewayContainerABI GatewayValueEntry GatewayValueContext
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceDecoded GatewayReferenceStackBound
  GatewayReferenceParserInputs GatewayReferenceParseResult GatewayReferenceParser GatewayReferenceAccountingStack GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayScalarDecoding GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_parser_reservations {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable mode_symbol
    (parser:forall bound,gateway_reference_short_parser backend python objects decimal_float detached io stable mode_symbol bound)
    ledger reserved arguments stream_block stream_offset initial readonly original before world events value after next:
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context(fun current object=>gateway_native_private(python current)object)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world->
  (forall object position,readonly object position->gateway_native_private(python world)object)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer+
    (if Val.eq value pointer then 1 else 0)<=python_native_strong(python next)pointer)%nat.
Proof.
  intros BUDGET MODE MODE_REGION STREAM INPUT READONLY RUN NONNULL.
  set(pointers:=reserved++map gateway_reference_pointer(gateway_reference_entries ledger)).
  assert(SCOPE:gateway_reference_scope python objects decimal_float(gateway_accounting_ledger pointers)[]world).
  { split;[|constructor]. intro pointer;rewrite gateway_accounting_count.
    unfold pointers;rewrite count_occ_app;exact(BUDGET pointer). }
  destruct(parser(S(length events))(gateway_accounting_stack pointers)(gateway_accounting_ledger pointers)[]arguments
    stream_block stream_offset initial readonly original before world events value after next
    (gateway_accounting_call pointers)(gateway_accounting_formed pointers)(gateway_accounting_bound pointers)SCOPE
    ltac:(intros captured MEMBER;inversion MEMBER)MODE MODE_REGION STREAM INPUT READONLY RUN NONNULL ltac:(lia))
    as(final &final_stream &wire &ticket &DECODED &FINAL_CONTEXT &FINAL_NATIVE &FINAL_DESCRIPTOR &FRAME).
  destruct DECODED as[FORMED ENTRIES FRESH OWNER BOUND HELD VALUE AVOIDS].
  intro pointer;pose proof(proj1 HELD pointer)as FIT.
  unfold gateway_reference_count in FIT;unfold gateway_reference_result_entries in ENTRIES;rewrite ENTRIES in FIT.
  cbn[gateway_reference_entry gateway_reference_pointer map]in FIT.
  change((if Val.eq value pointer then S(count_occ Val.eq(map gateway_reference_pointer(gateway_accounting_entries pointers))pointer)
    else count_occ Val.eq(map gateway_reference_pointer(gateway_accounting_entries pointers))pointer)<=python_native_strong(python next)pointer)%nat in FIT.
  rewrite gateway_accounting_pointers in FIT;unfold pointers in FIT;rewrite count_occ_app in FIT.
  unfold gateway_reference_count;destruct(Val.eq value pointer);lia.
Qed.

Section ActualReservations.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)(decimal_float:list Z->Floats.float->Prop)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop).
Let native:=fun current object=>gateway_native_private(python current)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (allocations:gateway_native_memory_runtime backend io native stable base heap_allocation)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
  (instances:gateway_instance_runtime backend(Clight.globalenv prog)python objects(fun _ _ _=>Logic.False))
  (errors:gateway_no_memory_runtime backend python)(projection:gateway_direct_io_projection backend io)
  (none_symbol mode_symbol:block)
  (constants:gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero))
  (NONE:Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol)
  (MODE_SYMBOL:Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol).

Theorem gateway_reference_actual_parser_reservations ledger reserved arguments stream_block stream_offset initial readonly original before world events value after next:
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world->
  (forall object position,readonly object position->native world object)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer+
    (if Val.eq value pointer then 1 else 0)<=python_native_strong(python next)pointer)%nat.
Proof.
  intros BUDGET MODE MODE_REGION STREAM INPUT READONLY RUN NONNULL.
  eapply gateway_reference_parser_reservations;try eassumption.
  intros bound;eapply gateway_reference_actual_short_parser;eassumption.
Qed.
End ActualReservations.

Definition gateway_reference_reserved_parse_result {World Event}(python:World->python_world)(objects:World->gateway_object_heap)
    decimal_float detached(io:Event->option gateway_native_io)(stable:World->block->Z->Prop)ge context ledger held reserved
    stream_block stream_offset initial readonly original events value after next:Prop:=
  exists final final_stream wire ticket,
    gateway_reference_decoded python objects decimal_float ge context ledger held wire ticket value final after next /\
    gateway_value_context(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset final_stream readonly original after next /\
    (forall object position,readonly object position->gateway_native_private(python next)object) /\
    stream_descriptor final_stream=stream_descriptor initial /\
    GatewayContainerEncoding.gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value wire)
      (gateway_received_bytes io(stream_descriptor initial)events) /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat).

Theorem gateway_reference_received_result_reservations {World Event}python objects decimal_float detached io stable ge context ledger held reserved
    stream_block stream_offset initial readonly original events value after next:
  @gateway_reference_parse_result World Event python objects decimal_float detached io stable ge context ledger held
    stream_block stream_offset initial readonly original events value after next->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer+
    (if Val.eq value pointer then 1 else 0)<=python_native_strong(python next)pointer)%nat)->
  gateway_reference_reserved_parse_result python objects decimal_float detached io stable ge context ledger held reserved
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros(final &final_stream &wire &ticket &DECODED &CONTEXT &NATIVE &DESCRIPTOR &FRAME)BUDGET.
  exists final,final_stream,wire,ticket;split;[exact DECODED|]. split;[exact CONTEXT|]. split;[exact NATIVE|].
  split;[exact DESCRIPTOR|]. split;[exact FRAME|]. intro pointer.
  pose proof(gateway_decoded_entries _ _ _ _ _ _ _ _ _ _ _ _ _ DECODED)as ENTRIES.
  unfold gateway_reference_count,gateway_reference_result_entries in *;rewrite ENTRIES.
  cbn[gateway_reference_entry gateway_reference_pointer map count_occ].
  specialize(BUDGET pointer);destruct(Val.eq value pointer);lia.
Qed.
