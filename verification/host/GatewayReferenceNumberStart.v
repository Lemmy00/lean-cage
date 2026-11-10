(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual zero/base allocations and setup guards produce the
   integer loop's operands from the same bounded input and source history. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceStackBound
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumberLiterals GatewayReferenceContainerScope GatewayReferenceEmptyContainer
  GatewayNumberConstruction GatewayNumberFailures GatewayNumberBaseFailure GatewayNumberIntegerStart GatewayNumberIntegerStructure GatewayNumberWidth
  GatewayContexts GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime GatewayPathEvents GatewayObjectRuns GatewayObjectEvents
  GatewayScalarConstructorCalls GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_start {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    ledger current_owner base_owner held definition parameters scalar slots stream_block stream_offset initial readonly original
    size object bytes digits before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_take current_owner(gateway_reference_entries ledger)=None->
  gateway_reference_take base_owner(gateway_reference_entries ledger)=None->current_owner<>base_owner->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_object_api_definition gateway_api_long_signed=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->0<=digits<Int64.unsigned size->Int64.unsigned size<=65536->
  parameters!_size=Some(Vlong size)->parameters!_digits=Some(Vlong(Int64.repr digits))->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate definition[Vlong Int64.zero](gateway_number_zero_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists initialized current current_offset base base_offset loop_parameters prefix suffix loop_memory loop_world,
    gateway_reference_ledger_well_formed initialized /\
    gateway_reference_entries initialized=
      gateway_reference_entry(S(gateway_reference_next ledger))base_owner(Vptr base base_offset)::
      gateway_reference_entry(gateway_reference_next ledger)current_owner(Vptr current current_offset)::gateway_reference_entries ledger /\
    gateway_reference_next initialized=S(S(gateway_reference_next ledger)) /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation initialized
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)(Vptr current current_offset)(gateway_long_object 0);
        gateway_reference_scalar_capture(S(gateway_reference_next ledger))(Vptr base base_offset)(gateway_long_object 1000000000)])
      scalar slots stream_block stream_offset initial readonly original size object bytes loop_memory loop_world /\
    loop_parameters!_value__1=Some(Vptr current current_offset) /\loop_parameters!_base=Some(Vptr base base_offset) /\
    loop_parameters!_index=Some(Vlong(Int64.repr digits)) /\
    loop_parameters!_width=Some(Vlong(Int64.repr(gateway_number_first_width(Int64.unsigned size-digits)))) /\
    loop_parameters!_size=Some(Vlong size) /\loop_parameters!_bytes=parameters!_bytes /\loop_parameters!_negative=parameters!_negative /\
    events=prefix++suffix /\gateway_received_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate definition[Vlong Int64.zero](gateway_number_zero_cont parameters)before)world)prefix
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env loop_parameters loop_memory)loop_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env loop_parameters loop_memory)loop_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros FORMED CURRENT_FREE BASE_FREE DISTINCT SCOPE DEFINITION INPUT DIGITS MAXIMUM SIZE_PARAMETER DIGITS_PARAMETER RUN NONNULL.
  destruct gateway_actual_number_constructor_bindings as[_[base_definition[BASE_DEFINITION[BASE_BINDING BASE_TYPE]]]].
  destruct BASE_BINDING as[base_symbol[BASE_SYMBOL BASE_FUNCTION]].
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vlong Int64.zero](gateway_number_zero_cont parameters)before world events
    (Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)RUN)
    as(allocating_zero &rest &zero &zero_after &zero_world &EVENTS &ZERO_RUN &REST).
  assert(ZERO_NONNULL:zero<>Vnullptr).
  { intro NULL;subst zero;apply NONNULL;eapply gateway_number_null_zero_denied;[exact BASE_SYMBOL|exact BASE_FUNCTION|exact BASE_TYPE|exact REST]. }
  destruct(gateway_reference_actual_literal_storage backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime constructors reference_threads false ledger current_owner held definition Int64.zero scalar slots stream_block stream_offset initial readonly original size object bytes
    before world allocating_zero zero zero_after zero_world FORMED CURRENT_FREE SCOPE DEFINITION INPUT ZERO_RUN ZERO_NONNULL)
    as(zero_ledger &ZERO_MINT &ZERO_WELL &ZERO_OWNED &ZERO_STORAGE &ZERO_SCOPE).
  change(Int64.signed Int64.zero)with 0 in ZERO_SCOPE.
  destruct(gateway_reference_mint_entries _ _ _ _ ZERO_MINT)as[ZERO_ENTRIES ZERO_NEXT].
  set(zero_capture:=gateway_reference_scalar_capture(gateway_reference_next ledger)zero(gateway_long_object 0)).
  set(zero_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation zero_ledger(held++[zero_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    zero_ledger(held++[zero_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as ZERO_CLOSED.
  destruct(gateway_number_base_source_path backend(Clight.globalenv prog)zero_property parameters zero zero_after base_symbol base_definition
    ZERO_CLOSED BASE_SYMBOL BASE_FUNCTION BASE_TYPE)as(base_parameters &BASE_PATH &BASE_CURRENT &BASE_PARAMETERS).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ BASE_PATH zero_after zero_world rest value after next
    (conj ZERO_STORAGE ZERO_SCOPE)REST)as(base_prefix &from_base &base_before &base_world &REST_EVENTS &BASE_QUIET &TO_BASE &BASE_READY &FROM_BASE).
  destruct(gateway_return_cut backend(Clight.globalenv prog)base_definition[Vlong(Int64.repr 1000000000)](gateway_number_base_cont base_parameters)
    base_before base_world from_base(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_BASE)
    as(allocating_base &from_setup &base_value &base_after &base_next &BASE_EVENTS &BASE_RUN &SETUP_RUN).
  assert(BASE_NONNULL:base_value<>Vnullptr).
  { intro NULL;subst base_value;apply NONNULL;exact(gateway_number_null_base_denied backend(Clight.globalenv prog)base_parameters base_after
      base_after base_next from_setup value after next SETUP_RUN). }
  assert(BASE_VACANT:gateway_reference_take base_owner(gateway_reference_entries zero_ledger)=None).
  { eapply GatewayReferenceStackBound.gateway_reference_mint_keeps_vacant;[exact BASE_FREE|exact DISTINCT|exact ZERO_MINT]. }
  destruct(gateway_reference_actual_literal_storage backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime constructors reference_threads true zero_ledger base_owner(held++[zero_capture])base_definition(Int64.repr 1000000000)scalar slots stream_block stream_offset
    initial readonly original size object bytes base_before base_world allocating_base base_value base_after base_next ZERO_WELL BASE_VACANT(proj2 BASE_READY)
    BASE_DEFINITION(proj1 BASE_READY)BASE_RUN BASE_NONNULL)
    as(initialized &BASE_MINT &WELL &BASE_OWNED &BASE_STORAGE &BASE_SCOPE).
  change(Int64.unsigned(Int64.repr 1000000000))with 1000000000 in BASE_SCOPE.
  destruct(gateway_reference_mint_entries _ _ _ _ BASE_MINT)as[BASE_ENTRIES BASE_NEXT].
  assert(CURRENT_OWNED:gateway_reference_owns initialized current_owner(gateway_reference_next ledger)zero).
  { unfold gateway_reference_owns;rewrite BASE_ENTRIES;right;exact ZERO_OWNED. }
  destruct(gateway_reference_owned_pointer python objects initialized current_owner(gateway_reference_next ledger)zero base_after base_next
    ltac:(eapply gateway_scalar_private_side;exact BASE_STORAGE)(proj1 BASE_SCOPE)CURRENT_OWNED)
    as(current &current_offset &CURRENT_POINTER &CURRENT_VALID);subst zero.
  destruct(gateway_reference_owned_pointer python objects initialized base_owner(gateway_reference_next zero_ledger)base_value base_after base_next
    ltac:(eapply gateway_scalar_private_side;exact BASE_STORAGE)(proj1 BASE_SCOPE)BASE_OWNED)
    as(base &base_offset &BASE_POINTER &BASE_VALID);subst base_value.
  set(base_capture:=gateway_reference_scalar_capture(gateway_reference_next zero_ledger)(Vptr base base_offset)(gateway_long_object 1000000000)).
  set(setup_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation initialized
    ((held++[zero_capture])++[base_capture])scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    initialized((held++[zero_capture])++[base_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as SETUP_CLOSED.
  assert(CURRENT_POINTER_VALID:forall memory current_world,setup_property memory current_world->
    Mem.weak_valid_pointer memory current(Ptrofs.unsigned current_offset)=true).
  { intros memory current_world[READY HOLD].
    destruct(gateway_reference_owned_pointer python objects initialized current_owner(gateway_reference_next ledger)(Vptr current current_offset)memory current_world
      ltac:(eapply gateway_scalar_private_side;exact READY)(proj1 HOLD)CURRENT_OWNED)as(candidate &offset &SAME &VALID);inversion SAME;subst;exact VALID. }
  assert(BASE_POINTER_VALID:forall memory current_world,setup_property memory current_world->
    Mem.weak_valid_pointer memory base(Ptrofs.unsigned base_offset)=true).
  { intros memory current_world[READY HOLD].
    destruct(gateway_reference_owned_pointer python objects initialized base_owner(gateway_reference_next zero_ledger)(Vptr base base_offset)memory current_world
      ltac:(eapply gateway_scalar_private_side;exact READY)(proj1 HOLD)BASE_OWNED)as(candidate &offset &SAME &VALID);inversion SAME;subst;exact VALID. }
  destruct(gateway_number_integer_start backend(Clight.globalenv prog)setup_property base_parameters current current_offset base base_offset
    (Int64.unsigned size)digits base_after SETUP_CLOSED DIGITS MAXIMUM CURRENT_POINTER_VALID BASE_POINTER_VALID BASE_CURRENT
    ltac:(rewrite BASE_PARAMETERS by discriminate;rewrite Int64.repr_unsigned;exact SIZE_PARAMETER)
    ltac:(rewrite BASE_PARAMETERS by discriminate;exact DIGITS_PARAMETER))
    as(loop_parameters &SETUP_PATH &LOOP_INDEX &LOOP_WIDTH &LOOP_BASE &LOOP_PARAMETERS).
  destruct(gateway_source_segment_cut backend(Clight.globalenv prog)_ _ _ _ SETUP_PATH base_after base_next from_setup value after next
    (conj BASE_STORAGE BASE_SCOPE)SETUP_RUN)as(setup_prefix &suffix &loop_memory &loop_world &SETUP_EVENTS &SETUP_QUIET &TO_LOOP &LOOP_READY &LOOP_REST).
  assert(ZERO_CALLER:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate definition[Vlong Int64.zero](gateway_number_zero_cont parameters)before)world)allocating_zero
    (gateway_live(Returnstate(Vptr current current_offset)(gateway_number_zero_cont parameters)zero_after)zero_world)).
  { exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(gateway_number_zero_cont parameters)ltac:(cbn;exact I)ZERO_RUN). }
  assert(BASE_CALLER:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate base_definition[Vlong(Int64.repr 1000000000)](gateway_number_base_cont base_parameters)base_before)base_world)allocating_base
    (gateway_live(Returnstate(Vptr base base_offset)(gateway_number_base_cont base_parameters)base_after)base_next)).
  { exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(gateway_number_base_cont base_parameters)ltac:(cbn;exact I)BASE_RUN). }
  exists initialized,current,current_offset,base,base_offset,loop_parameters,
    (allocating_zero++base_prefix++allocating_base++setup_prefix),suffix,loop_memory,loop_world.
  split;[exact WELL|]. split;[rewrite BASE_ENTRIES,ZERO_ENTRIES,ZERO_NEXT;reflexivity|].
  split;[rewrite BASE_NEXT,ZERO_NEXT;reflexivity|]. split.
  - rewrite<-ZERO_NEXT;split;[exact(proj1 LOOP_READY)|].
    pose proof(proj2 LOOP_READY)as FINAL_SCOPE.
    change(gateway_reference_scope python objects decimal_float initialized((held++[zero_capture])++[base_capture])loop_world)in FINAL_SCOPE.
    rewrite<-app_assoc in FINAL_SCOPE;exact FINAL_SCOPE.
  - split;[rewrite LOOP_PARAMETERS by discriminate;exact BASE_CURRENT|]. split;[exact LOOP_BASE|].
    split;[exact LOOP_INDEX|]. split;[exact LOOP_WIDTH|]. split.
    + rewrite LOOP_PARAMETERS by discriminate;rewrite BASE_PARAMETERS by discriminate;exact SIZE_PARAMETER.
    + split;[rewrite LOOP_PARAMETERS by discriminate;rewrite BASE_PARAMETERS by discriminate;reflexivity|].
      split;[rewrite LOOP_PARAMETERS by discriminate;rewrite BASE_PARAMETERS by discriminate;reflexivity|].
      split;[rewrite EVENTS,REST_EVENTS,BASE_EVENTS,SETUP_EVENTS;repeat rewrite app_assoc;reflexivity|]. split.
      * rewrite!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)base_prefix BASE_QUIET),
          (gateway_quiet_received io(stream_descriptor initial)setup_prefix SETUP_QUIET).
        rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_long_signed definition[Vlong Int64.zero]
          before world allocating_zero(Vptr current current_offset)zero_after zero_world(stream_descriptor initial)projection DEFINITION ZERO_RUN).
        rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_long_unsigned base_definition[Vlong(Int64.repr 1000000000)]
          base_before base_world allocating_base(Vptr base base_offset)base_after base_next(stream_descriptor initial)projection BASE_DEFINITION BASE_RUN);reflexivity.
      * split;[|exact LOOP_REST]. repeat eapply gateway_steps_append;
          [exact ZERO_CALLER|exact TO_BASE|exact BASE_CALLER|exact TO_LOOP].
Qed.
