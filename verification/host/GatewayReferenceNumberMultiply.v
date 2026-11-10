(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One real integer iteration multiplies its retained operands,
   releases exactly the prior value and reaches the actual addition with the new root. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceNumericLedger GatewayReferenceNumericFrames
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumericRelease GatewayReferenceNumberArithmetic GatewayReferenceContainerScope
  GatewayReferenceEmptyContainer GatewayReferenceFloatTail GatewayNumberIntegerCalls GatewayNumberIntegerStructure GatewayNumberArithmeticSuccess
  GatewayNumberArithmeticBindings GatewayContexts GatewaySourcePaths GatewayFramedRuntime GatewayPathEvents GatewayObjectRuns GatewayObjectEvents
  GatewayScalarConstructorCalls GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_multiply {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    ledger current_owner current_ticket current current_offset accumulator scaled_owner base_ticket base base_offset part_ticket part part_offset chunk
    held parameters scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger current_owner current_ticket(Vptr current current_offset)->
  gateway_reference_take scaled_owner(gateway_reference_entries ledger)=None->
  (forall captured,In captured held->gateway_held_ticket captured<>current_ticket)->
  In(gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000))held->
  In(gateway_reference_scalar_capture part_ticket(Vptr part part_offset)(gateway_long_object chunk))held->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object accumulator)])world->
  parameters!_value__1=Some(Vptr current current_offset)->parameters!_base=Some(Vptr base base_offset)->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vptr part part_offset)(number_integer_part_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final scaled scaled_offset add_definition called_parameters prefix suffix add_before add_world,
    gateway_object_api_definition gateway_api_number_add=Some add_definition /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final scaled_owner(gateway_reference_next ledger)(Vptr scaled scaled_offset) /\
    gateway_reference_take current_owner(gateway_reference_entries final)=None /\
    (forall owner ticket pointer,ticket<>current_ticket->gateway_reference_owns ledger owner ticket pointer->
      gateway_reference_owns final owner ticket pointer) /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)(Vptr scaled scaled_offset)(gateway_long_object(accumulator*1000000000))])
      scalar slots stream_block stream_offset initial readonly original size object bytes add_before add_world /\
    called_parameters!_scaled=Some(Vptr scaled scaled_offset) /\called_parameters!_part=Some(Vptr part part_offset) /\
    (forall identifier,identifier<>_part->identifier<>_t'18->identifier<>_scaled->identifier<>_t'19->
      called_parameters!identifier=parameters!identifier) /\
    events=prefix++suffix /\gateway_received_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vptr part part_offset)(number_integer_part_cont parameters)before)world)prefix
      (gateway_live(Callstate add_definition[Vptr scaled scaled_offset;Vptr part part_offset](number_integer_add_cont called_parameters)add_before)add_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate add_definition[Vptr scaled scaled_offset;Vptr part part_offset](number_integer_add_cont called_parameters)add_before)add_world)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_reference_next final=S(gateway_reference_next ledger) /\
    exists constructed,
      gateway_reference_apply(gateway_reference_mint scaled_owner(Vptr scaled scaled_offset))(gateway_reference_valid ledger)=gateway_reference_valid constructed /\
      gateway_reference_apply(gateway_reference_release current_owner(Vptr current current_offset))(gateway_reference_valid constructed)=gateway_reference_valid final.
Proof.
  intros FORMED CURRENT_OWNED FREE DIFFERENT BASE PART SCOPE CURRENT_PARAMETER BASE_PARAMETER INPUT RUN NONNULL.
  set(current_capture:=gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object accumulator)).
  set(property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger(held++[current_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    ledger(held++[current_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  assert(PART_VALID:forall memory current_world,property memory current_world->Mem.weak_valid_pointer memory part(Ptrofs.unsigned part_offset)=true).
  { intros memory current_world[READY HOLD].
    destruct(gateway_reference_capture_member _ _ _ _ _ _ _ HOLD ltac:(apply in_or_app;left;exact PART))as[[owner OWNED]OTHER].
    destruct(gateway_reference_owned_pointer python objects ledger owner part_ticket(Vptr part part_offset)memory current_world
      ltac:(eapply gateway_scalar_private_side;exact READY)(proj1 HOLD)OWNED)as(candidate &offset &SAME &VALID);inversion SAME;subst;exact VALID. }
  destruct gateway_actual_number_multiply_binding as[multiply_definition[MULTIPLY_DEFINITION[MULTIPLY_BINDING MULTIPLY_TYPE]]].
  destruct MULTIPLY_BINDING as[multiply_symbol[MULTIPLY_SYMBOL MULTIPLY_FUNCTION]].
  destruct gateway_actual_number_add_binding as[add_definition[ADD_DEFINITION[ADD_BINDING ADD_TYPE]]].
  destruct ADD_BINDING as[add_symbol[ADD_SYMBOL ADD_FUNCTION]].
  destruct gateway_actual_number_float_bindings as[_[release_definition[RELEASE_DEFINITION[RELEASE_BINDING RELEASE_TYPE]]]].
  destruct RELEASE_BINDING as[release_symbol[RELEASE_SYMBOL RELEASE_FUNCTION]].
  destruct(gateway_number_multiply_source_path backend(Clight.globalenv prog)property parameters part part_offset(Vptr current current_offset)(Vptr base base_offset)
    before multiply_symbol multiply_definition CLOSED PART_VALID CURRENT_PARAMETER BASE_PARAMETER ltac:(right;repeat eexists;reflexivity)
    ltac:(right;repeat eexists;reflexivity)MULTIPLY_SYMBOL MULTIPLY_FUNCTION MULTIPLY_TYPE)
    as(multiply_parameters &MULTIPLY_PATH &MULTIPLY_PART &MULTIPLY_PARAMETERS).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ MULTIPLY_PATH before world events value after next(conj INPUT SCOPE)RUN)
    as(source_prefix &rest &multiply_before &multiply_world &EVENTS &SOURCE_QUIET &TO_MULTIPLY &MULTIPLY_READY &FROM_MULTIPLY).
  destruct(gateway_return_cut backend(Clight.globalenv prog)multiply_definition[Vptr current current_offset;Vptr base base_offset]
    (number_integer_multiply_cont multiply_parameters)multiply_before multiply_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_MULTIPLY)
    as(multiplying &from_multiply &scaled_value &multiply_after &multiply_next &MULTIPLY_EVENTS &MULTIPLY_RUN &MULTIPLY_REST).
  assert(SCALED_NONNULL:scaled_value<>Vnullptr).
  { eapply gateway_number_scaled_success_nonnull;[rewrite MULTIPLY_PARAMETERS by discriminate;exact CURRENT_PARAMETER|
      right;repeat eexists;reflexivity|exact RELEASE_SYMBOL|exact RELEASE_FUNCTION|exact RELEASE_TYPE|exact MULTIPLY_REST|exact NONNULL]. }
  destruct(gateway_reference_actual_binary_storage backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime constructors reference_threads true ledger scaled_owner(held++[current_capture])multiply_definition current_ticket(Vptr current current_offset)accumulator
    base_ticket(Vptr base base_offset)1000000000 scalar slots stream_block stream_offset initial readonly original size object bytes
    multiply_before multiply_world multiplying scaled_value multiply_after multiply_next FORMED FREE(proj2 MULTIPLY_READY)
    ltac:(apply in_or_app;right;left;reflexivity)ltac:(apply in_or_app;left;exact BASE)MULTIPLY_DEFINITION(proj1 MULTIPLY_READY)MULTIPLY_RUN SCALED_NONNULL)
    as(constructed &MINT &WELL &SCALED_OWNED &MULTIPLY_STORAGE &MULTIPLY_SCOPE).
  set(scaled_capture:=gateway_reference_scalar_capture(gateway_reference_next ledger)scaled_value(gateway_long_object(accumulator*1000000000))).
  set(release_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation constructed
    ((held++[current_capture])++[scaled_capture])scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    constructed((held++[current_capture])++[scaled_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as RELEASE_CLOSED.
  destruct(gateway_number_old_value_release_path backend(Clight.globalenv prog)release_property multiply_parameters(Vptr current current_offset)scaled_value
    multiply_after release_symbol release_definition RELEASE_CLOSED
    ltac:(rewrite MULTIPLY_PARAMETERS by discriminate;exact CURRENT_PARAMETER)ltac:(right;repeat eexists;reflexivity)
    RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE)as(release_parameters &RELEASE_PATH &RELEASE_SCALED &RELEASE_PARAMETERS).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ RELEASE_PATH multiply_after multiply_next from_multiply value after next
    (conj MULTIPLY_STORAGE MULTIPLY_SCOPE)MULTIPLY_REST)
    as(release_prefix &from_release &release_before &release_world &RELEASE_EVENTS &RELEASE_QUIET &TO_RELEASE &RELEASE_READY &FROM_RELEASE).
  destruct(gateway_return_cut backend(Clight.globalenv prog)release_definition[Vptr current current_offset](number_integer_release_value_cont release_parameters)
    release_before release_world from_release(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &from_add &ignored &release_after &release_next &RELEASE_RUN_EVENTS &RELEASE_RUN &RELEASE_REST).
  assert(TICKET_BOUND:(current_ticket<gateway_reference_next ledger)%nat).
  { exact(proj1(Forall_forall _ _)(proj2(proj2 FORMED))_ CURRENT_OWNED). }
  assert(CURRENT_STILL:gateway_reference_owns constructed current_owner current_ticket(Vptr current current_offset)).
  { eapply gateway_reference_numeric_minted_keeps;[exact MINT|exact CURRENT_OWNED]. }
  assert(REORDERED:gateway_reference_scope python objects decimal_float constructed((held++[scaled_capture])++[current_capture])release_world).
  { eapply gateway_reference_scope_sublist;[exact(proj2 RELEASE_READY)|]. intros captured MEMBER;
      repeat rewrite in_app_iff in *;cbn in *;tauto. }
  destruct(gateway_reference_actual_numeric_release backend(Clight.globalenv prog)python objects detached io stable thread_errno heap_allocation decimal_float
    runtime references reference_threads constructed current_owner current_ticket(Vptr current current_offset)(gateway_long_object accumulator)
    (held++[scaled_capture])release_definition scalar slots stream_block stream_offset initial readonly original size object bytes
    release_before release_world releasing ignored release_after release_next WELL CURRENT_STILL
    ltac:(intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|BAD]];
      [apply DIFFERENT;exact OLD|subst captured;cbn;lia|contradiction])REORDERED RELEASE_DEFINITION(proj1 RELEASE_READY)RELEASE_RUN)
    as(final &RELEASE &FINAL_WELL &FINAL_SCOPE &FINAL_STORAGE &OCCURRENCE).
  assert(FINAL_SCALED:gateway_reference_owns final scaled_owner(gateway_reference_next ledger)scaled_value).
  { eapply gateway_reference_numeric_released_keeps;[exact WELL|exact CURRENT_STILL|lia|exact RELEASE|exact SCALED_OWNED]. }
  assert(CURRENT_VACANT:gateway_reference_take current_owner(gateway_reference_entries final)=None).
  { eapply gateway_reference_numeric_released_vacant;[exact WELL|exact RELEASE]. }
  destruct(gateway_reference_owned_pointer python objects final scaled_owner(gateway_reference_next ledger)scaled_value release_after release_next
    ltac:(eapply gateway_scalar_private_side;exact FINAL_STORAGE)(proj1 FINAL_SCOPE)FINAL_SCALED)
    as(scaled &scaled_offset &SCALED_POINTER &SCALED_VALID);subst scaled_value.
  set(add_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final(held++[scaled_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    final(held++[scaled_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as ADD_CLOSED.
  assert(VALID:forall memory current_world,add_property memory current_world->Mem.weak_valid_pointer memory scaled(Ptrofs.unsigned scaled_offset)=true).
  { intros memory current_world[READY HOLD].
    destruct(gateway_reference_owned_pointer python objects final scaled_owner(gateway_reference_next ledger)(Vptr scaled scaled_offset)memory current_world
      ltac:(eapply gateway_scalar_private_side;exact READY)(proj1 HOLD)FINAL_SCALED)as(candidate &offset &SAME &OBSERVED);inversion SAME;subst;exact OBSERVED. }
  destruct(gateway_number_add_source_path backend(Clight.globalenv prog)add_property release_parameters scaled scaled_offset(Vptr part part_offset)ignored
    release_after add_symbol add_definition ADD_CLOSED VALID RELEASE_SCALED
    ltac:(rewrite RELEASE_PARAMETERS by discriminate;exact MULTIPLY_PART)ltac:(right;repeat eexists;reflexivity)
    ADD_SYMBOL ADD_FUNCTION ADD_TYPE)as(called_parameters &ADD_PATH &ADD_PARAMETERS).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ ADD_PATH release_after release_next from_add value after next
    (conj FINAL_STORAGE FINAL_SCOPE)RELEASE_REST)as(add_prefix &suffix &add_before &add_world &ADD_EVENTS &ADD_QUIET &TO_ADD &ADD_READY &ADD_REST).
  pose proof(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(number_integer_multiply_cont multiply_parameters)ltac:(cbn;exact I)MULTIPLY_RUN)as MULTIPLY_CALLER.
  pose proof(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(number_integer_release_value_cont release_parameters)ltac:(cbn;exact I)RELEASE_RUN)as RELEASE_CALLER.
  exists final,scaled,scaled_offset,add_definition,called_parameters,
    (source_prefix++multiplying++release_prefix++releasing++add_prefix),suffix,add_before,add_world.
  split;[exact ADD_DEFINITION|]. split;[exact FINAL_WELL|]. split;[exact FINAL_SCALED|]. split;[exact CURRENT_VACANT|]. split.
  - intros owner ticket pointer OTHER OWNED;eapply gateway_reference_numeric_released_keeps;
      [exact WELL|exact CURRENT_STILL|exact OTHER|exact RELEASE|].
    eapply gateway_reference_numeric_minted_keeps;[exact MINT|exact OWNED].
  - split;[exact ADD_READY|]. split;[rewrite ADD_PARAMETERS;exact RELEASE_SCALED|].
    split;[rewrite ADD_PARAMETERS;rewrite RELEASE_PARAMETERS by discriminate;exact MULTIPLY_PART|]. split.
    + intros identifier A B C D;rewrite ADD_PARAMETERS;rewrite RELEASE_PARAMETERS by assumption;rewrite MULTIPLY_PARAMETERS by assumption;reflexivity.
    + split;[rewrite EVENTS,MULTIPLY_EVENTS,RELEASE_EVENTS,RELEASE_RUN_EVENTS,ADD_EVENTS;repeat rewrite app_assoc;reflexivity|]. split.
      * rewrite!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)source_prefix SOURCE_QUIET),
          (gateway_quiet_received io(stream_descriptor initial)release_prefix RELEASE_QUIET),
          (gateway_quiet_received io(stream_descriptor initial)add_prefix ADD_QUIET).
        rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_number_multiply multiply_definition
          [Vptr current current_offset;Vptr base base_offset]multiply_before multiply_world multiplying(Vptr scaled scaled_offset)multiply_after multiply_next
          (stream_descriptor initial)projection MULTIPLY_DEFINITION MULTIPLY_RUN).
        rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_decref release_definition[Vptr current current_offset]
          release_before release_world releasing ignored release_after release_next(stream_descriptor initial)projection RELEASE_DEFINITION RELEASE_RUN);reflexivity.
      * split.
        -- repeat eapply gateway_steps_append;
             [exact TO_MULTIPLY|exact MULTIPLY_CALLER|exact TO_RELEASE|exact RELEASE_CALLER|exact TO_ADD].
        -- split;[exact ADD_REST|]. split.
           ++ rewrite(gateway_reference_numeric_release_next _ _ _ _ RELEASE);exact(proj2(gateway_reference_mint_entries _ _ _ _ MINT)).
           ++ exists constructed;split;assumption.
Qed.
