(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual float-construction suffix retains its operands,
   consumes the selected text reference and returns the same single SDK conversion. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumericRelease GatewayReferenceFloat GatewayReferenceContainerScope
  GatewayReferenceEmptyContainer GatewayNumberFloatSource GatewayNumberFloatReturn GatewayNumberConstruction GatewayBindings
  GatewayScalarConstructorCalls GatewayScalarLength GatewayObjectExecution GatewayObjectRuns GatewayObjectEvents GatewayContexts GatewaySourcePaths
  GatewayFramedRuntime GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_actual_number_float_bindings:
  (exists definition,gateway_object_api_definition gateway_api_float_string=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyFloat_FromString definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default) /\
  (exists definition,gateway_object_api_definition gateway_api_decref=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_Py_DecRef definition /\
    type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default).
Proof.
  split;eexists;split;[reflexivity| |reflexivity|];split;
    first[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.

Theorem gateway_reference_actual_float_tail {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    ledger text_owner text_ticket text characters result_owner held parameters scalar slots stream_block stream_offset initial readonly original
    size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger text_owner text_ticket text->
  gateway_reference_take result_owner(gateway_reference_entries ledger)=None->
  (forall captured,In captured held->gateway_held_ticket captured<>text_ticket)->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_scalar_capture text_ticket text(gateway_unicode_object characters)])world->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate text(gateway_number_decode_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final floating constructed,
    decimal_float characters floating /\
    gateway_reference_apply(gateway_reference_mint result_owner value)(gateway_reference_valid ledger)=gateway_reference_valid constructed /\
    gateway_reference_apply(gateway_reference_release text_owner text)(gateway_reference_valid constructed)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final result_owner(gateway_reference_next ledger)value /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)value(gateway_float_object floating)])
      scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros FORMED TEXT_OWNED VACANT DIFFERENT SCOPE INPUT RUN NONNULL.
  set(text_capture:=gateway_reference_scalar_capture text_ticket text(gateway_unicode_object characters)).
  set(property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger(held++[text_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    ledger(held++[text_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  destruct(gateway_reference_owned_pointer python objects ledger text_owner text_ticket text before world
    ltac:(eapply gateway_scalar_private_side;exact INPUT)(proj1 SCOPE)TEXT_OWNED)as(text_block &text_offset &TEXT_POINTER &TEXT_VALID).
  subst text.
  assert(POINTER:forall memory current,property memory current->Mem.weak_valid_pointer memory text_block(Ptrofs.unsigned text_offset)=true).
  { intros memory current[READY HOLD].
    destruct(gateway_reference_owned_pointer python objects ledger text_owner text_ticket(Vptr text_block text_offset)memory current
      ltac:(eapply gateway_scalar_private_side;exact READY)(proj1 HOLD)TEXT_OWNED)as(candidate &offset &SAME &VALID).
    inversion SAME;subst;exact VALID. }
  destruct gateway_actual_number_float_bindings as
    [[float_definition[FLOAT_DEFINITION[FLOAT_BINDING FLOAT_TYPE]]]
     [release_definition[RELEASE_DEFINITION[RELEASE_BINDING RELEASE_TYPE]]]].
  destruct FLOAT_BINDING as[float_symbol[FLOAT_SYMBOL FLOAT_FUNCTION]].
  destruct RELEASE_BINDING as[release_symbol[RELEASE_SYMBOL RELEASE_FUNCTION]].
  destruct(gateway_number_float_source_path backend(Clight.globalenv prog)property parameters text_block text_offset before float_symbol float_definition
    CLOSED POINTER FLOAT_SYMBOL FLOAT_FUNCTION FLOAT_TYPE)as(float_parameters &FLOAT_PATH &FLOAT_TEXT &FLOAT_PARAMETERS).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ FLOAT_PATH before world events value after next(conj INPUT SCOPE)RUN)
    as(prefix &rest &float_before &float_world &EVENTS &PREFIX_QUIET &PREFIX &FLOAT_READY &FROM_FLOAT).
  destruct(gateway_return_cut backend(Clight.globalenv prog)float_definition[Vptr text_block text_offset](gateway_number_float_cont float_parameters)
    float_before float_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_FLOAT)
    as(converting &from_float &returned &float_after &float_next &REST_EVENTS &CONVERT &REST).
  pose proof(gateway_number_after_float_identity backend(Clight.globalenv prog)float_parameters(Vptr text_block text_offset)returned
    float_after float_next from_float value after next release_symbol release_definition FLOAT_TEXT
    ltac:(right;repeat eexists;reflexivity)RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE REST)as SAME;subst returned.
  destruct(gateway_reference_actual_float_storage backend(Clight.globalenv prog)python objects detached io stable thread_errno heap_allocation
    decimal_float runtime constructors reference_threads ledger result_owner(held++[text_capture])text_ticket(Vptr text_block text_offset)characters
    float_definition scalar slots stream_block stream_offset initial readonly original size object bytes float_before float_world converting value float_after float_next
    FORMED VACANT(proj2 FLOAT_READY)ltac:(apply in_or_app;right;left;reflexivity)FLOAT_DEFINITION(proj1 FLOAT_READY)CONVERT NONNULL)
    as(floating &constructed &DECIMAL &MINT &WELL &RESULT_OWNED &FLOAT_STORAGE &FLOAT_SCOPE).
  set(float_capture:=gateway_reference_scalar_capture(gateway_reference_next ledger)value(gateway_float_object floating)).
  set(after_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation constructed
    ((held++[text_capture])++[float_capture])scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    constructed((held++[text_capture])++[float_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as AFTER_CLOSED.
  destruct(gateway_number_text_release_source_path backend(Clight.globalenv prog)after_property float_parameters(Vptr text_block text_offset)value
    float_after release_symbol release_definition AFTER_CLOSED FLOAT_TEXT ltac:(right;repeat eexists;reflexivity)RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE)
    as(release_parameters &RELEASE_PATH &RELEASE_VALUE &RELEASE_PARAMETERS).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ RELEASE_PATH float_after float_next from_float value after next
    (conj FLOAT_STORAGE FLOAT_SCOPE)REST)as(source_prefix &from_release &release_before &release_world &FLOAT_EVENTS &RELEASE_QUIET &TO_RELEASE &RELEASE_READY &FROM_RELEASE).
  destruct(gateway_return_cut backend(Clight.globalenv prog)release_definition[Vptr text_block text_offset](gateway_number_text_release_cont release_parameters)
    release_before release_world from_release(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &suffix &ignored &release_after &release_next &RELEASE_EVENTS &RELEASE_RUN &FINAL_RUN).
  assert(TEXT_BOUND:(text_ticket<gateway_reference_next ledger)%nat).
  { exact(proj1(Forall_forall _ _)(proj2(proj2 FORMED))_ TEXT_OWNED). }
  assert(TEXT_STILL:gateway_reference_owns constructed text_owner text_ticket(Vptr text_block text_offset)).
  { destruct(gateway_reference_mint_entries _ _ _ _ MINT)as[ENTRIES COUNT]. unfold gateway_reference_owns;rewrite ENTRIES;right;exact TEXT_OWNED. }
  assert(RELEASE_SCOPE:gateway_reference_scope python objects decimal_float constructed((held++[float_capture])++[text_capture])release_world).
  { eapply gateway_reference_scope_sublist;[exact(proj2 RELEASE_READY)|].
    intros captured MEMBER;repeat rewrite in_app_iff in *;cbn in *;tauto. }
  destruct(gateway_reference_actual_numeric_release backend(Clight.globalenv prog)python objects detached io stable thread_errno heap_allocation decimal_float
    runtime references reference_threads constructed text_owner text_ticket(Vptr text_block text_offset)(gateway_unicode_object characters)
    (held++[float_capture])release_definition scalar slots stream_block stream_offset initial readonly original size object bytes
    release_before release_world releasing ignored release_after release_next WELL TEXT_STILL
    ltac:(intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|BAD]];
      [apply DIFFERENT;exact OLD|subst captured;cbn;lia|contradiction])RELEASE_SCOPE RELEASE_DEFINITION(proj1 RELEASE_READY)RELEASE_RUN)
    as(final &RELEASE &FINAL_WELL &FINAL_SCOPE &FINAL_STORAGE &OCCURRENCE).
  assert(FINAL_OWNED:gateway_reference_owns final result_owner(gateway_reference_next ledger)value).
  { destruct(gateway_reference_release_selected constructed text_owner text_ticket(Vptr text_block text_offset)WELL TEXT_STILL)
      as(selected &APPLY &SELECTED_WELL &ABSENT &RETAINED &COUNTS).
    rewrite RELEASE in APPLY;injection APPLY as EQUAL;subst selected;apply RETAINED;[lia|exact RESULT_OWNED]. }
  destruct(gateway_reference_owned_pointer python objects final result_owner(gateway_reference_next ledger)value release_after release_next
    ltac:(eapply gateway_scalar_private_side;exact FINAL_STORAGE)(proj1 FINAL_SCOPE)FINAL_OWNED)as(result_block &result_offset &RESULT_POINTER &RESULT_VALID).
  set(final_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final(held++[float_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    final(held++[float_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as FINAL_CLOSED.
  destruct(gateway_number_float_return_ready backend(Clight.globalenv prog)final_property FINAL_CLOSED release_parameters value ignored
    release_after release_next suffix value after next RELEASE_VALUE ltac:(right;repeat eexists;exact RESULT_POINTER)
    (conj FINAL_STORAGE FINAL_SCOPE)FINAL_RUN)as[RETURNED[FINAL_READY FINAL_QUIET]].
  exists final,floating,constructed;split;[exact DECIMAL|]. split;[exact MINT|]. split;[exact RELEASE|].
  split;[exact FINAL_WELL|]. split;[exact FINAL_OWNED|]. split;[exact FINAL_READY|].
  rewrite EVENTS,REST_EVENTS,FLOAT_EVENTS,RELEASE_EVENTS,!gateway_received_append,
    (gateway_quiet_received io(stream_descriptor initial)prefix PREFIX_QUIET),
    (gateway_quiet_received io(stream_descriptor initial)source_prefix RELEASE_QUIET),
    (gateway_quiet_received io(stream_descriptor initial)suffix FINAL_QUIET).
  rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_float_string float_definition[Vptr text_block text_offset]
    float_before float_world converting value float_after float_next(stream_descriptor initial)projection FLOAT_DEFINITION CONVERT).
  rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_decref release_definition[Vptr text_block text_offset]
    release_before release_world releasing ignored release_after release_next(stream_descriptor initial)projection RELEASE_DEFINITION RELEASE_RUN).
  reflexivity.
Qed.
