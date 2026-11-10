(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Strict UTF-8 scalar results retain their actual source reference. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayScalarLength
  GatewayScalarBuffer GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarSizedFrames GatewayScalarTextCall
  GatewayScalarReadPath GatewayScalarBytesPath GatewayScalarText GatewayScalarDecoding GatewayScalarConstructorCalls GatewayRegionThreads
  GatewayNativeRegions GatewayNativeMemory GatewayObjectEvents GatewayObjectRuns GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceScalarStorage GatewayReferenceScalarCleanup GatewayThreadInvariant.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_text_value {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (io_projection:gateway_direct_io_projection backend io)
    context ledger held slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next mode_symbol :
  Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall candidate position,gateway_scalar_mode_region mode_symbol candidate position->readonly candidate position)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->Int64.unsigned size<=16777216 ->
  gateway_scalar_payload_ready(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)heap_allocation gateway_scalar_text slots stream_block stream_offset initial readonly original
    size object bytes before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists final characters,
    gateway_utf8_text bytes characters /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_unicode_object characters)|}])next /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    gateway_value_heap decimal_float(objects next)value(gateway_wire_scalar 4 bytes) /\
    gateway_received_bytes io(stream_descriptor initial)events=[] /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_result(gateway_reference_depth context))value)
      (gateway_reference_valid ledger)=gateway_reference_valid final.
Proof.
  intros MODE_SYMBOL MODE SUBSET FORMED VACANT SCOPE BUFFER MAXIMUM INPUT READONLY RUN NONNULL.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    reference_threads ledger held runtime)as SCOPED_RUNTIME.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPED_RUNTIME readonly)as THREADS.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { destruct INPUT as[[[[[[SIDE[STREAM[STABLE[RAW FRAME]]]]SLOTS]TAG]SIZE]REST]PAYLOAD].
    intros candidate position READ;split;
      [exact(gateway_value_readonly_live _ _ _ _ _ RAW candidate position READ)|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED_INPUT:gateway_scalar_payload_ready native stable augmented heap_allocation gateway_scalar_text slots stream_block stream_offset
    initial readonly original size object bytes before world).
  { destruct INPUT as[READY PAYLOAD];split;[|exact PAYLOAD]. pose proof READY as[_[[SIDE HEAP]SEPARATE]].
    eapply gateway_scalar_buffer_rebase;[exact READY|]. split;[split;[exact SIDE|exact SCOPE]|exact OWNED]. }
  destruct(gateway_actual_text_constructor_cut backend io native stable augmented thread_errno THREADS heap_allocation slots parameters
    stream_block stream_offset initial readonly original size object bytes before world events value after next mode_symbol MODE_SYMBOL BUFFER AUGMENTED_INPUT RUN NONNULL)
    as(definition &called_parameters &prefix &constructing &suffix &constructor_before &constructor_world &constructor_after &constructor_next &
      DEFINITION &EVENTS &QUIET &CALLED_BUFFER &AUGMENTED_READY &CONSTRUCTOR_RUN &REST).
  pose proof(gateway_scalar_terminated_side native stable augmented heap_allocation gateway_scalar_text slots stream_block stream_offset initial readonly original
    size object bytes constructor_before constructor_world AUGMENTED_READY)as[CALLED_SIDE CALLED_OWNED].
  assert(READY:gateway_scalar_private_ready python objects detached stable heap_allocation gateway_scalar_text slots stream_block stream_offset
    initial readonly original size object bytes constructor_before constructor_world).
  { split;[eapply gateway_scalar_terminated_rebase;[exact AUGMENTED_READY|exact(proj1 CALLED_SIDE)]|].
    intros candidate position READ;exact(proj2(CALLED_OWNED candidate position READ)). }
  destruct(gateway_actual_utf8_scalar_bytes backend(Clight.globalenv prog)python objects detached decimal_float io stable thread_errno runtime constructors
    definition heap_allocation gateway_scalar_text slots stream_block stream_offset initial readonly original size object bytes constructor_before constructor_world
    constructing value constructor_after constructor_next mode_symbol DEFINITION READY MAXIMUM MODE SUBSET CONSTRUCTOR_RUN NONNULL)
    as[characters DECODED].
  destruct(gateway_reference_actual_scalar_storage backend(Clight.globalenv prog)python objects detached io stable thread_errno
    heap_allocation decimal_float runtime constructors reference_threads ledger(gateway_reference_result(gateway_reference_depth context))held
    gateway_api_unicode_utf8 definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero](gateway_unicode_object characters)gateway_unicode_kind
    gateway_scalar_text slots stream_block stream_offset initial readonly original size object bytes constructor_before constructor_world
    constructing value constructor_after constructor_next FORMED VACANT(proj2 CALLED_SIDE)DEFINITION
    ltac:(intros;split;[eapply gateway_scalar_text_request;[eassumption|exact MAXIMUM|exact DECODED|exact MODE|exact SUBSET]|exact I])eq_refl eq_refl
    ltac:(unfold gateway_destructor_kind;auto 9)READY CONSTRUCTOR_RUN NONNULL)
    as[final[MINT[WELL[OWNED_RESULT[AFTER_READY HELD_SCOPE]]]]].
  destruct(gateway_reference_actual_scalar_cleanup backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations reference_threads final
    (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
      gateway_held_view:=gateway_held_scalar_value(gateway_unicode_object characters)|}])_t'21 gateway_scalar_text slots called_parameters
    stream_block stream_offset initial readonly original size object constructor_after constructor_next suffix value value after next
    ltac:(discriminate)CALLED_BUFFER(proj1(proj1(proj1 AFTER_READY)))HELD_SCOPE(proj2 AFTER_READY)REST)
    as[SAME[[FINAL_CONTEXT[HELD_FINAL READONLY_FINAL]]CLEANUP_EMPTY]].
  assert(LOOKUP:gateway_object_values(objects next)value=Some(gateway_unicode_object characters)).
  { pose proof(proj2 HELD_FINAL)as CAPTURED;apply Forall_app in CAPTURED;destruct CAPTURED as[OLD NEW].
    destruct(Forall_inv NEW)as[CAPTURED_OWNER[PRIVATE[DESTRUCTIBLE[DESCRIBED CHILDREN]]]];exact DESCRIBED. }
  exists final,characters;split;[exact DECODED|]. split;[exact WELL|]. split;[exact OWNED_RESULT|].
  split;[apply gateway_reference_result_binding|]. split;[exact HELD_FINAL|]. split;[exact FINAL_CONTEXT|].
  split;[exact READONLY_FINAL|].
  split;[eapply gateway_heap_scalar;[exact LOOKUP|apply gateway_scalar_unicode;exact DECODED]|]. split;[|exact MINT].
  rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),CLEANUP_EMPTY.
  rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_unicode_utf8 definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]
    constructor_before constructor_world constructing value constructor_after constructor_next(stream_descriptor initial)io_projection DEFINITION CONSTRUCTOR_RUN).
  reflexivity.
Qed.
