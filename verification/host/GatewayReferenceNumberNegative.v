(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual negation mints its own reference, releases the prior
   operand and transfers the selected signed result through the real source return. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceMoves GatewayReferenceNormalForm
  GatewayReferenceNumericLedger GatewayReferenceNumericFrames GatewayReferenceNumericNormalForm GatewayReferenceNumericContext GatewayReferenceNumericRequests
  GatewayReferenceNumericRelease GatewayReferenceNumberOwners GatewayReferenceNumberArithmetic GatewayReferenceNumberReturn GatewayReferenceContainerScope GatewayReferenceEmptyContainer
  GatewayReferenceFloatTail GatewayNumberSignSource GatewayNumberNegativeResult GatewayNumberArithmeticBindings GatewayNumberIntegerStructure
  GatewayContexts GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime GatewayPathEvents GatewayObjectRuns GatewayObjectEvents
  GatewayScalarConstructorCalls GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_negative {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    invocation ledger current_ticket current current_offset integer tail held parameters ignored
    scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry current_ticket(number_current_owner invocation)(Vptr current current_offset)::tail->
  gateway_reference_take(number_signed_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries ledger)=None->
  (forall captured,In captured held->gateway_held_ticket captured<>current_ticket)->
  gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger
    (held++[gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object integer)])
    scalar slots stream_block stream_offset initial readonly original size object bytes before world->
  parameters!_negative=Some(Vint Int.one)->parameters!_value__1=Some(Vptr current current_offset)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate ignored(number_sign_base_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final,
    gateway_reference_ledger_well_formed final /\gateway_reference_next final=S(gateway_reference_next ledger) /\
    gateway_reference_entries final=gateway_reference_entry(gateway_reference_next ledger)(gateway_reference_result invocation)value::tail /\
    gateway_reference_owns final(gateway_reference_result invocation)(gateway_reference_next ledger)value /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)value(gateway_long_object(-integer))])
      scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros FORMED ENTRIES SIGNED_FREE RESULT_FREE DIFFERENT INPUT NEGATIVE CURRENT RUN NONNULL.
  set(current_capture:=gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object integer)).
  set(property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger(held++[current_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    ledger(held++[current_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  destruct gateway_actual_number_negative_binding as[definition[DEFINITION[BINDING TYPE]]];destruct BINDING as[symbol[SYMBOL FUNCTION]].
  destruct gateway_actual_number_float_bindings as[_[release_definition[RELEASE_DEFINITION[RELEASE_BINDING RELEASE_TYPE]]]].
  destruct RELEASE_BINDING as[release_symbol[RELEASE_SYMBOL RELEASE_FUNCTION]].
  pose proof(gateway_number_negative_source_path backend(Clight.globalenv prog)property parameters(Vptr current current_offset)ignored before symbol definition
    CLOSED NEGATIVE CURRENT ltac:(right;repeat eexists;reflexivity)SYMBOL FUNCTION TYPE)as PATH.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(source_prefix &rest &negative_before &negative_world &EVENTS &SOURCE_QUIET &TO_NEGATIVE &NEGATIVE_READY &FROM_NEGATIVE).
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vptr current current_offset](number_sign_negative_cont parameters)
    negative_before negative_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_NEGATIVE)
    as(negating &from_release &returned &negative_after &negative_next &NEGATIVE_EVENTS &NEGATIVE_RUN &NEGATIVE_REST).
  pose proof(gateway_number_negative_result_identity backend(Clight.globalenv prog)parameters(Vptr current current_offset)returned negative_after negative_next from_release
    value after next release_symbol release_definition CURRENT ltac:(right;repeat eexists;reflexivity)RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE NEGATIVE_REST)
    as SAME;subst returned.
  destruct(gateway_reference_actual_negative_storage backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime constructors reference_threads ledger(number_signed_owner invocation)(held++[current_capture])definition current_ticket(Vptr current current_offset)integer
    scalar slots stream_block stream_offset initial readonly original size object bytes negative_before negative_world negating value negative_after negative_next
    FORMED SIGNED_FREE(proj2 NEGATIVE_READY)ltac:(apply in_or_app;right;left;reflexivity)DEFINITION(proj1 NEGATIVE_READY)NEGATIVE_RUN NONNULL)
    as(constructed &MINT &WELL &SIGNED_OWNED &NEGATIVE_STORAGE &NEGATIVE_SCOPE).
  set(signed_capture:=gateway_reference_scalar_capture(gateway_reference_next ledger)value(gateway_long_object(-integer))).
  set(release_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation constructed
    ((held++[current_capture])++[signed_capture])scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    constructed((held++[current_capture])++[signed_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as RELEASE_CLOSED.
  destruct(gateway_number_negative_release_path backend(Clight.globalenv prog)release_property parameters(Vptr current current_offset)value negative_after
    release_symbol release_definition RELEASE_CLOSED CURRENT ltac:(right;repeat eexists;reflexivity)RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE)
    as(release_parameters &RELEASE_PATH &SIGNED_PARAMETER &RELEASE_PARAMETERS).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ RELEASE_PATH negative_after negative_next from_release value after next
    (conj NEGATIVE_STORAGE NEGATIVE_SCOPE)NEGATIVE_REST)
    as(release_prefix &release_events &release_before &release_world &RELEASE_EVENTS &RELEASE_QUIET &TO_RELEASE &RELEASE_READY &FROM_RELEASE).
  destruct(gateway_return_cut backend(Clight.globalenv prog)release_definition[Vptr current current_offset](number_sign_old_cont release_parameters)
    release_before release_world release_events(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &from_return &release_ignored &release_after &release_next &RELEASE_RUN_EVENTS &RELEASE_RUN &RELEASE_REST).
  assert(CURRENT_OWNED:gateway_reference_owns ledger(number_current_owner invocation)current_ticket(Vptr current current_offset))
    by(unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity).
  assert(CURRENT_STILL:gateway_reference_owns constructed(number_current_owner invocation)current_ticket(Vptr current current_offset)).
  { eapply gateway_reference_numeric_minted_keeps;[exact MINT|exact CURRENT_OWNED]. }
  assert(TICKET_BOUND:(current_ticket<gateway_reference_next ledger)%nat)
    by(exact(proj1(Forall_forall _ _)(proj2(proj2 FORMED))_ CURRENT_OWNED)).
  assert(REORDERED:gateway_reference_scope python objects decimal_float constructed((held++[signed_capture])++[current_capture])release_world).
  { eapply gateway_reference_scope_sublist;[exact(proj2 RELEASE_READY)|]. intros captured MEMBER;
      repeat rewrite in_app_iff in *;cbn in *;tauto. }
  destruct(gateway_reference_actual_numeric_release backend(Clight.globalenv prog)python objects detached io stable thread_errno heap_allocation decimal_float
    runtime references reference_threads constructed(number_current_owner invocation)current_ticket(Vptr current current_offset)(gateway_long_object integer)
    (held++[signed_capture])release_definition scalar slots stream_block stream_offset initial readonly original size object bytes
    release_before release_world releasing release_ignored release_after release_next WELL CURRENT_STILL
    ltac:(intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|BAD]];
      [apply DIFFERENT;exact OLD|subst captured;cbn;lia|contradiction])REORDERED RELEASE_DEFINITION(proj1 RELEASE_READY)RELEASE_RUN)
    as(released &RELEASE &RELEASED_WELL &RELEASED_SCOPE &RELEASED_STORAGE &OCCURRENCE).
  assert(SIGNED_STILL:gateway_reference_owns released(number_signed_owner invocation)(gateway_reference_next ledger)value).
  { eapply gateway_reference_numeric_released_keeps;[exact WELL|exact CURRENT_STILL|lia|exact RELEASE|exact SIGNED_OWNED]. }
  destruct(gateway_reference_mint_entries _ _ _ _ MINT)as[MINT_ENTRIES MINT_NEXT].
  destruct(gateway_reference_numeric_middle_release constructed released tail(gateway_reference_next ledger)(number_signed_owner invocation)value
    current_ticket(number_current_owner invocation)(Vptr current current_offset)
    ltac:(unfold number_signed_owner,number_current_owner;discriminate)ltac:(rewrite MINT_ENTRIES,ENTRIES;reflexivity)RELEASE)
    as[RELEASED_ENTRIES RELEASED_NEXT].
  destruct(gateway_reference_owned_pointer python objects released(number_signed_owner invocation)(gateway_reference_next ledger)value release_after release_next
    ltac:(eapply gateway_scalar_private_side;exact RELEASED_STORAGE)(proj1 RELEASED_SCOPE)SIGNED_STILL)
    as(result &result_offset &RESULT_POINTER &RESULT_VALID);subst value.
  set(return_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation released(held++[signed_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    released(held++[signed_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as RETURN_CLOSED.
  pose proof(gateway_number_negative_return_path backend(Clight.globalenv prog)return_property release_parameters(Vptr result result_offset)release_ignored
    release_after RETURN_CLOSED SIGNED_PARAMETER)as RETURN_PATH.
  destruct(gateway_source_segment_cut backend(Clight.globalenv prog)_ _ _ _ RETURN_PATH release_after release_next from_return(Vptr result result_offset)after next
    (conj RELEASED_STORAGE RELEASED_SCOPE)RELEASE_REST)
    as(assign_prefix &return_events &return_before &return_world &RETURN_EVENTS &RETURN_QUIET &TO_RETURN &RETURN_READY &FINAL_RUN).
  assert(CURRENT_VACANT:gateway_reference_take(number_current_owner invocation)(gateway_reference_entries released)=None).
  { eapply gateway_reference_numeric_released_vacant;[exact WELL|exact RELEASE]. }
  destruct(gateway_reference_move_scope python objects decimal_float released(number_signed_owner invocation)(number_current_owner invocation)
    (gateway_reference_next ledger)(Vptr result result_offset)(held++[signed_capture])return_world
    RELEASED_WELL SIGNED_STILL CURRENT_VACANT(proj2 RETURN_READY))
    as(moved &MOVE &MOVED_WELL &MOVED_CURRENT &MOVED_SCOPE &COUNTS &OTHERS).
  destruct(gateway_reference_head_move _ _ _ _ _ _ _ RELEASED_ENTRIES MOVE)as[MOVED_ENTRIES MOVED_NEXT].
  assert(FINAL_VACANT:gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries moved)=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite MOVED_ENTRIES in MEMBER;destruct MEMBER as[HEAD|OLD].
    - subst entry;cbn in OWNER;unfold number_current_owner in OWNER;discriminate.
    - apply(proj1(gateway_reference_take_none _ _)RESULT_FREE entry);[rewrite ENTRIES;right;exact OLD|exact OWNER]. }
  destruct(gateway_reference_actual_number_return backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    invocation moved(gateway_reference_next ledger)(held++[signed_capture])(PTree.set _value__1(Vptr result result_offset)release_parameters)(Vptr result result_offset)
    scalar slots stream_block stream_offset initial readonly original size object bytes return_before return_world return_events(Vptr result result_offset)after next
    MOVED_WELL MOVED_CURRENT FINAL_VACANT ltac:(apply PTree.gss)ltac:(right;repeat eexists;reflexivity)
    (conj(proj1 RETURN_READY)MOVED_SCOPE)FINAL_RUN)
    as(final &RETURNED &RETURN_MOVE &FINAL_WELL &FINAL_OWNED &FINAL_READY &FINAL_EMPTY).
  destruct(gateway_reference_head_move _ _ _ _ _ _ _ MOVED_ENTRIES RETURN_MOVE)as[FINAL_ENTRIES FINAL_NEXT].
  exists final;split;[exact FINAL_WELL|]. split;[rewrite FINAL_NEXT,MOVED_NEXT,RELEASED_NEXT,MINT_NEXT;reflexivity|].
  split;[exact FINAL_ENTRIES|]. split;[exact FINAL_OWNED|]. split;[exact FINAL_READY|].
  rewrite EVENTS,NEGATIVE_EVENTS,RELEASE_EVENTS,RELEASE_RUN_EVENTS,RETURN_EVENTS,!gateway_received_append,
    (gateway_quiet_received io(stream_descriptor initial)source_prefix SOURCE_QUIET),
    (gateway_quiet_received io(stream_descriptor initial)release_prefix RELEASE_QUIET),
    (gateway_quiet_received io(stream_descriptor initial)assign_prefix RETURN_QUIET),FINAL_EMPTY.
  rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_number_negative definition[Vptr current current_offset]
    negative_before negative_world negating(Vptr result result_offset)negative_after negative_next(stream_descriptor initial)projection DEFINITION NEGATIVE_RUN).
  rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_decref release_definition[Vptr current current_offset]
    release_before release_world releasing release_ignored release_after release_next(stream_descriptor initial)projection RELEASE_DEFINITION RELEASE_RUN);reflexivity.
Qed.
