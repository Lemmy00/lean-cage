(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One complete integer iteration connects its actual payload
   slice, arithmetic, selected releases, next source state and exact older reference tail. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceStackBound
  GatewayReferenceNumericLedger GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumberOwners GatewayReferenceNumberNormalForm GatewayReferenceMoves
  GatewayReferenceNumberPart GatewayReferenceNumberMultiply GatewayReferenceNumberAdd GatewayReferenceContainerScope GatewayReferenceAncestors
  GatewayNumberIntegerStructure GatewayScalarConstructorCalls GatewayFramedRuntime GatewayPathEvents GatewayObjectEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_iteration {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    invocation ledger base_ticket base base_offset current_ticket current current_offset accumulator tail held parameters index width prefix_bytes chunk suffix_bytes
    scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(number_base_owner invocation)base_ticket(Vptr base base_offset)->
  gateway_reference_owns ledger(number_current_owner invocation)current_ticket(Vptr current current_offset)->
  gateway_reference_take(number_current_owner invocation)(gateway_reference_entries ledger)=
    Some(gateway_reference_entry current_ticket(number_current_owner invocation)(Vptr current current_offset),tail)->
  gateway_reference_take(number_part_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(number_scaled_owner invocation)(gateway_reference_entries ledger)=None->
  (forall captured,In captured held->gateway_held_ticket captured<>current_ticket)->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000);
      gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object accumulator)])world->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->Int64.unsigned size<=65536->
  bytes=prefix_bytes++chunk++suffix_bytes->index=Z.of_nat(length prefix_bytes)->width=Z.of_nat(length chunk)->0<width<=9->
  Forall(fun byte=>48<=Byte.unsigned byte<=57)chunk->
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!_index=Some(Vlong(Int64.repr index))->
  parameters!_width=Some(Vlong(Int64.repr width))->parameters!_size=Some(Vlong size)->
  parameters!_base=Some(Vptr base base_offset)->parameters!_value__1=Some(Vptr current current_offset)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final result result_offset loop_parameters prefix suffix loop_memory loop_world,
    gateway_reference_ledger_well_formed final /\gateway_reference_next final=S(S(S(gateway_reference_next ledger))) /\
    gateway_reference_entries final=gateway_reference_entry(S(S(gateway_reference_next ledger)))(number_current_owner invocation)(Vptr result result_offset)::tail /\
    gateway_reference_owns final(number_base_owner invocation)base_ticket(Vptr base base_offset) /\
    gateway_reference_owns final(number_current_owner invocation)(S(S(gateway_reference_next ledger)))(Vptr result result_offset) /\
    gateway_reference_take(number_part_owner invocation)(gateway_reference_entries final)=None /\
    gateway_reference_take(number_scaled_owner invocation)(gateway_reference_entries final)=None /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000);
        gateway_reference_scalar_capture(S(S(gateway_reference_next ledger)))(Vptr result result_offset)
          (gateway_long_object(accumulator*1000000000+gateway_decimal_value chunk))])
      scalar slots stream_block stream_offset initial readonly original size object bytes loop_memory loop_world /\
    loop_parameters!_value__1=Some(Vptr result result_offset) /\loop_parameters!_index=Some(Vlong(Int64.repr(index+width))) /\
    loop_parameters!_width=Some(Vlong(Int64.repr 9)) /\loop_parameters!_base=Some(Vptr base base_offset) /\
    loop_parameters!_size=Some(Vlong size) /\loop_parameters!_bytes=parameters!_bytes /\
    loop_parameters!_negative=parameters!_negative /\loop_parameters!_digits=parameters!_digits /\
    events=prefix++suffix /\gateway_received_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env parameters before)world)prefix
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env loop_parameters loop_memory)loop_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env loop_parameters loop_memory)loop_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros FORMED BASE_OWNED CURRENT_OWNED TAKE PART_FREE SCALED_FREE DIFFERENT SCOPE INPUT MAXIMUM BYTES POSITION WIDTH WIDTH_BOUND DIGITS
    BUFFER INDEX LIMIT SIZE BASE_PARAMETER CURRENT_PARAMETER RUN NONNULL.
  set(base_capture:=gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000)).
  set(current_capture:=gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object accumulator)).
  assert(CURRENT_BOUND:(current_ticket<gateway_reference_next ledger)%nat)
    by(exact(proj1(Forall_forall _ _)(proj2(proj2 FORMED))_ CURRENT_OWNED)).
  assert(BASE_BOUND:(base_ticket<gateway_reference_next ledger)%nat)
    by(exact(proj1(Forall_forall _ _)(proj2(proj2 FORMED))_ BASE_OWNED)).
  assert(BASE_DIFFERENT:base_ticket<>current_ticket).
  { intro SAME;rewrite SAME in BASE_OWNED.
    destruct(gateway_reference_owned_ticket_unique _ _ _ _ _ _ FORMED CURRENT_OWNED BASE_OWNED)as[OWNER POINTER].
    unfold number_base_owner,number_current_owner in OWNER;discriminate. }
  destruct(gateway_reference_actual_number_part backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors reference_threads
    projection ledger(number_part_owner invocation)(held++[base_capture;current_capture])parameters index width prefix_bytes chunk suffix_bytes
    scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next
    FORMED PART_FREE SCOPE INPUT MAXIMUM BYTES POSITION WIDTH WIDTH_BOUND DIGITS BUFFER INDEX LIMIT SIZE RUN NONNULL)
    as(part_ledger &part &part_offset &part_parameters &part_prefix &from_part &part_after &part_next &PART_MINT &PART_WELL &PART_OWNED &PART_READY &PART_PARAMETERS &EVENTS &PART_EMPTY &TO_PART &PART_REST).
  destruct(gateway_reference_mint_entries _ _ _ _ PART_MINT)as[PART_ENTRIES PART_NEXT].
  assert(CURRENT_STILL:gateway_reference_owns part_ledger(number_current_owner invocation)current_ticket(Vptr current current_offset)).
  { eapply gateway_reference_numeric_minted_keeps;[exact PART_MINT|exact CURRENT_OWNED]. }
  assert(SCALED_VACANT:gateway_reference_take(number_scaled_owner invocation)(gateway_reference_entries part_ledger)=None).
  { eapply(GatewayReferenceStackBound.gateway_reference_mint_keeps_vacant ledger part_ledger
      (number_part_owner invocation)(Vptr part part_offset)(number_scaled_owner invocation));
      [exact SCALED_FREE|unfold number_part_owner,number_scaled_owner;discriminate|exact PART_MINT]. }
  set(part_capture:=gateway_reference_scalar_capture(gateway_reference_next ledger)(Vptr part part_offset)(gateway_long_object(gateway_decimal_value chunk))).
  set(multiply_held:=held++[base_capture;part_capture]).
  assert(MULTIPLY_SCOPE:gateway_reference_scope python objects decimal_float part_ledger(multiply_held++[current_capture])part_next).
  { eapply gateway_reference_scope_sublist;[exact(proj2 PART_READY)|]. intros captured MEMBER;
      unfold multiply_held in *;repeat rewrite in_app_iff in *;cbn in *;tauto. }
  destruct(gateway_reference_actual_number_multiply backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
    projection part_ledger(number_current_owner invocation)current_ticket current current_offset accumulator(number_scaled_owner invocation)
    base_ticket base base_offset(gateway_reference_next ledger)part part_offset(gateway_decimal_value chunk)multiply_held part_parameters
    scalar slots stream_block stream_offset initial readonly original size object bytes part_after part_next from_part value after next
    PART_WELL CURRENT_STILL SCALED_VACANT
    ltac:(intros captured MEMBER;unfold multiply_held in MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|[SAME|BAD]]];
      [apply DIFFERENT;exact OLD|subst captured;exact BASE_DIFFERENT|subst captured;cbn;lia|contradiction])
    ltac:(unfold multiply_held;apply in_or_app;right;left;reflexivity)
    ltac:(unfold multiply_held;apply in_or_app;right;right;left;reflexivity)MULTIPLY_SCOPE
    ltac:(rewrite PART_PARAMETERS by discriminate;exact CURRENT_PARAMETER)
    ltac:(rewrite PART_PARAMETERS by discriminate;exact BASE_PARAMETER)(proj1 PART_READY)PART_REST NONNULL)
    as(multiplied &scaled &scaled_offset &add_definition &add_parameters &multiply_prefix &from_add &add_before &add_world &ADD_DEFINITION &MULTIPLY_WELL
      &SCALED_OWNED &CURRENT_FREE &MULTIPLY_RETAINED &ADD_READY &ADD_SCALED &ADD_PART &MULTIPLY_PARAMETERS &MULTIPLY_EVENTS &MULTIPLY_EMPTY &TO_ADD &ADD_REST
      &MULTIPLY_NEXT &scaled_ledger &SCALED_MINT &CURRENT_RELEASE).
  assert(PART_STILL:gateway_reference_owns multiplied(number_part_owner invocation)(gateway_reference_next ledger)(Vptr part part_offset)).
  { apply MULTIPLY_RETAINED;[lia|exact PART_OWNED]. }
  set(add_held:=held++[base_capture]).
  set(scaled_capture:=gateway_reference_scalar_capture(gateway_reference_next part_ledger)(Vptr scaled scaled_offset)
    (gateway_long_object(accumulator*1000000000))).
  assert(SUM_SCOPE:gateway_reference_scope python objects decimal_float multiplied(add_held++[part_capture;scaled_capture])add_world).
  { eapply gateway_reference_scope_sublist;[exact(proj2 ADD_READY)|]. intros captured MEMBER;
      unfold add_held,multiply_held in *;repeat rewrite in_app_iff in *;cbn in *;tauto. }
  destruct(gateway_reference_actual_number_add backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
    projection multiplied(number_current_owner invocation)(number_part_owner invocation)(gateway_reference_next ledger)part part_offset(gateway_decimal_value chunk)
    (number_scaled_owner invocation)(gateway_reference_next part_ledger)scaled scaled_offset(accumulator*1000000000)add_held add_parameters add_definition index width
    scalar slots stream_block stream_offset initial readonly original size object bytes add_before add_world from_add value after next
    MULTIPLY_WELL CURRENT_FREE PART_STILL SCALED_OWNED ltac:(rewrite PART_NEXT;lia)
    ltac:(intros captured MEMBER;unfold add_held in MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|BAD]];
      [pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger(held++[base_capture;current_capture])world captured FORMED SCOPE
        ltac:(apply in_or_app;left;exact OLD))as BOUND;rewrite PART_NEXT;lia|
       subst captured;cbn;rewrite PART_NEXT;lia|contradiction])SUM_SCOPE ADD_DEFINITION ADD_SCALED ADD_PART
    ltac:(rewrite MULTIPLY_PARAMETERS by discriminate;rewrite PART_PARAMETERS by discriminate;exact INDEX)
    ltac:(rewrite MULTIPLY_PARAMETERS by discriminate;rewrite PART_PARAMETERS by discriminate;exact LIMIT)(proj1 ADD_READY)ADD_REST NONNULL)
    as(final &result &result_offset &loop_parameters &add_prefix &suffix &loop_memory &loop_world &FINAL_WELL &FINAL_NEXT &RESULT_OWNED &FINAL_PART_FREE
      &FINAL_SCALED_FREE &ADD_RETAINED &LOOP_READY &LOOP_VALUE &LOOP_INDEX &LOOP_WIDTH &LOOP_PARAMETERS &ADD_EVENTS &ADD_EMPTY &TO_LOOP &LOOP_REST
      &summed_ledger &scaled_released &SUM_MINT &SCALED_RELEASE &PART_RELEASE).
  assert(TICKET:gateway_reference_next multiplied=S(S(gateway_reference_next ledger)))by(rewrite MULTIPLY_NEXT,PART_NEXT;reflexivity).
  assert(BASE_STILL:gateway_reference_owns multiplied(number_base_owner invocation)base_ticket(Vptr base base_offset)).
  { apply MULTIPLY_RETAINED;[exact BASE_DIFFERENT|]. eapply gateway_reference_numeric_minted_keeps;[exact PART_MINT|exact BASE_OWNED]. }
  assert(FINAL_BASE:gateway_reference_owns final(number_base_owner invocation)base_ticket(Vptr base base_offset)).
  { apply ADD_RETAINED;[lia|rewrite PART_NEXT;lia|exact BASE_STILL]. }
  assert(FINAL_ENTRIES:gateway_reference_entries final=
    gateway_reference_entry(gateway_reference_next multiplied)(number_current_owner invocation)(Vptr result result_offset)::tail).
  { eapply gateway_number_iteration_reference_tail;
      [exact TAKE|exact PART_MINT|exact SCALED_MINT|exact CURRENT_RELEASE|exact SUM_MINT|exact SCALED_RELEASE|exact PART_RELEASE]. }
  exists final,result,result_offset,loop_parameters,(part_prefix++multiply_prefix++add_prefix),suffix,loop_memory,loop_world.
  split;[exact FINAL_WELL|]. split;[rewrite FINAL_NEXT,TICKET;reflexivity|].
  split;[rewrite<-TICKET;exact FINAL_ENTRIES|]. split;[exact FINAL_BASE|].
  split;[rewrite<-TICKET;exact RESULT_OWNED|]. split;[exact FINAL_PART_FREE|]. split;[exact FINAL_SCALED_FREE|]. split.
  - rewrite<-TICKET;split;[exact(proj1 LOOP_READY)|].
    pose proof(proj2 LOOP_READY)as HELD;unfold add_held in HELD;rewrite<-app_assoc in HELD;exact HELD.
  - split;[exact LOOP_VALUE|]. split;[exact LOOP_INDEX|]. split;[exact LOOP_WIDTH|]. split.
    + rewrite LOOP_PARAMETERS by discriminate;rewrite MULTIPLY_PARAMETERS by discriminate;rewrite PART_PARAMETERS by discriminate;exact BASE_PARAMETER.
    + split.
      * rewrite LOOP_PARAMETERS by discriminate;rewrite MULTIPLY_PARAMETERS by discriminate;rewrite PART_PARAMETERS by discriminate;exact SIZE.
      * split.
        -- rewrite LOOP_PARAMETERS by discriminate;rewrite MULTIPLY_PARAMETERS by discriminate;rewrite PART_PARAMETERS by discriminate;reflexivity.
        -- split.
           ++ rewrite LOOP_PARAMETERS by discriminate;rewrite MULTIPLY_PARAMETERS by discriminate;rewrite PART_PARAMETERS by discriminate;reflexivity.
           ++ split.
              ** rewrite LOOP_PARAMETERS by discriminate;rewrite MULTIPLY_PARAMETERS by discriminate;rewrite PART_PARAMETERS by discriminate;reflexivity.
              ** split;[rewrite EVENTS,MULTIPLY_EVENTS,ADD_EVENTS;repeat rewrite app_assoc;reflexivity|]. split.
                 --- rewrite!gateway_received_append,PART_EMPTY,MULTIPLY_EMPTY,ADD_EMPTY;reflexivity.
                 --- split;[eapply gateway_steps_append;[exact TO_PART|eapply gateway_steps_append;[exact TO_ADD|exact TO_LOOP]]|exact LOOP_REST].
Qed.
