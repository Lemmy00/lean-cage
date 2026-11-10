(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual chunked integer construction computes the entire
   same digit payload, performs its source sign cleanup and returns one owned result. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceAncestors
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumberOwners GatewayReferenceNumberVacancy GatewayReferenceNumberStart
  GatewayReferenceNumberIteration GatewayReferenceNumberFold GatewayReferenceNumberSign GatewayReferenceContainerScope
  GatewayNumber GatewayNumberWidth GatewayNumberFoldMath GatewayNumberConstruction GatewayNumberIntegerStructure
  GatewayScalarConstructorCalls GatewayFramedRuntime GatewayPathEvents GatewayObjectEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_integer_construction {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    (negative:bool)invocation ledger held definition parameters prefix_bytes digits scalar slots stream_block stream_offset initial readonly original
    size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_take(number_current_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(number_base_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(number_part_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(number_scaled_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(number_signed_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_object_api_definition gateway_api_long_signed=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->Int64.unsigned size<=65536->bytes=prefix_bytes++digits->digits<>[]->
  Forall(fun byte=>48<=Byte.unsigned byte<=57)digits->
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!_size=Some(Vlong size)->
  parameters!_digits=Some(Vlong(Int64.repr(Z.of_nat(length prefix_bytes))))->
  parameters!_negative=Some(Vint(if negative then Int.one else Int.zero))->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate definition[Vlong Int64.zero](gateway_number_zero_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final ticket,
    gateway_reference_ledger_well_formed final /\(gateway_reference_next ledger<=ticket)%nat /\
    gateway_reference_entries final=gateway_reference_entry ticket(gateway_reference_result invocation)value::gateway_reference_entries ledger /\
    gateway_reference_owns final(gateway_reference_result invocation)ticket value /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture ticket value
        (gateway_long_object(if negative then -gateway_decimal_value digits else gateway_decimal_value digits))])
      scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros FORMED CURRENT_FREE BASE_FREE PART_FREE SCALED_FREE SIGNED_FREE RESULT_FREE SCOPE DEFINITION INPUT MAXIMUM BYTES NONEMPTY DIGITS
    BUFFER SIZE DIGITS_PARAMETER NEGATIVE RUN NONNULL.
  pose proof INPUT as[[[STORAGE[COUNT LOAD]]TERMINATED]PRIVATE].
  assert(DIGIT_COUNT:Int64.unsigned size-Z.of_nat(length prefix_bytes)=Z.of_nat(length digits)).
  { rewrite BYTES,length_app,Nat2Z.inj_add in COUNT;lia. }
  assert(POSITIVE:0<Z.of_nat(length digits))by(destruct digits;[contradiction|cbn;lia]).
  destruct(gateway_reference_actual_number_start backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors reference_threads
    projection ledger(number_current_owner invocation)(number_base_owner invocation)held definition parameters scalar slots stream_block stream_offset initial readonly original
    size object bytes(Z.of_nat(length prefix_bytes))before world events value after next FORMED CURRENT_FREE BASE_FREE
    ltac:(unfold number_current_owner,number_base_owner;discriminate)SCOPE DEFINITION INPUT ltac:(lia)MAXIMUM SIZE DIGITS_PARAMETER RUN NONNULL)
    as(initialized &current &current_offset &base &base_offset &loop_parameters &setup_prefix &loop_events &loop_memory &loop_world &INITIALIZED_WELL &INITIALIZED_ENTRIES
      &INITIALIZED_NEXT &INITIALIZED_READY &LOOP_VALUE &LOOP_BASE &LOOP_INDEX &LOOP_WIDTH &LOOP_SIZE &LOOP_BYTES &LOOP_NEGATIVE &EVENTS &SETUP_EMPTY &TO_LOOP &LOOP_RUN).
  set(width:=gateway_number_first_width(Z.of_nat(length digits))).
  pose proof(gateway_number_first_width_bounds(Z.of_nat(length digits))POSITIVE)as[WIDTH_BOUND WIDTH_FITS].
  set(chunk:=firstn(Z.to_nat width)digits);set(remaining:=skipn(Z.to_nat width)digits).
  assert(SPLIT:digits=chunk++remaining)by(symmetry;apply firstn_skipn).
  assert(CHUNK_LENGTH:Z.of_nat(length chunk)=width).
  { unfold chunk;rewrite length_firstn,Nat.min_l by lia;rewrite Z2Nat.id by lia;reflexivity. }
  pose proof DIGITS as ALL_DIGITS;rewrite SPLIT in ALL_DIGITS;apply Forall_app in ALL_DIGITS;destruct ALL_DIGITS as[CHUNK_DIGITS REMAINING_DIGITS].
  set(base_capture:=gateway_reference_scalar_capture(S(gateway_reference_next ledger))(Vptr base base_offset)(gateway_long_object 1000000000)).
  set(current_capture:=gateway_reference_scalar_capture(gateway_reference_next ledger)(Vptr current current_offset)(gateway_long_object 0)).
  assert(INITIALIZED_SCOPE:gateway_reference_scope python objects decimal_float initialized(held++[base_capture;current_capture])loop_world).
  { eapply gateway_reference_scope_sublist;[exact(proj2 INITIALIZED_READY)|]. intros captured MEMBER;
      repeat rewrite in_app_iff in *;cbn in *;tauto. }
  assert(INITIALIZED_BASE:gateway_reference_owns initialized(number_base_owner invocation)(S(gateway_reference_next ledger))(Vptr base base_offset))
    by(unfold gateway_reference_owns;rewrite INITIALIZED_ENTRIES;left;reflexivity).
  assert(INITIALIZED_CURRENT:gateway_reference_owns initialized(number_current_owner invocation)(gateway_reference_next ledger)(Vptr current current_offset))
    by(unfold gateway_reference_owns;rewrite INITIALIZED_ENTRIES;right;left;reflexivity).
  set(stable_tail:=gateway_reference_entry(S(gateway_reference_next ledger))(number_base_owner invocation)(Vptr base base_offset)::gateway_reference_entries ledger).
  assert(INITIALIZED_TAKE:gateway_reference_take(number_current_owner invocation)(gateway_reference_entries initialized)=
    Some(gateway_reference_entry(gateway_reference_next ledger)(number_current_owner invocation)(Vptr current current_offset),stable_tail)).
  { rewrite INITIALIZED_ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
    destruct(gateway_reference_place_eq(number_current_owner invocation)(number_base_owner invocation));[unfold number_current_owner,number_base_owner in e;discriminate|].
    destruct(gateway_reference_place_eq(number_current_owner invocation)(number_current_owner invocation));[reflexivity|congruence]. }
  assert(INITIALIZED_PART:gateway_reference_take(number_part_owner invocation)(gateway_reference_entries initialized)=None).
  { rewrite INITIALIZED_ENTRIES;apply gateway_number_two_heads_vacant;
      [unfold number_base_owner,number_part_owner;discriminate|unfold number_current_owner,number_part_owner;discriminate|exact PART_FREE]. }
  assert(INITIALIZED_SCALED:gateway_reference_take(number_scaled_owner invocation)(gateway_reference_entries initialized)=None).
  { rewrite INITIALIZED_ENTRIES;apply gateway_number_two_heads_vacant;
      [unfold number_base_owner,number_scaled_owner;discriminate|unfold number_current_owner,number_scaled_owner;discriminate|exact SCALED_FREE]. }
  destruct(gateway_reference_actual_number_iteration backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
    projection invocation initialized(S(gateway_reference_next ledger))base base_offset(gateway_reference_next ledger)current current_offset 0 stable_tail held
    loop_parameters(Z.of_nat(length prefix_bytes))width prefix_bytes chunk remaining scalar slots stream_block stream_offset initial readonly original size object bytes
    loop_memory loop_world loop_events value after next INITIALIZED_WELL INITIALIZED_BASE INITIALIZED_CURRENT INITIALIZED_TAKE INITIALIZED_PART INITIALIZED_SCALED
    ltac:(intros captured MEMBER;pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger held world captured FORMED SCOPE MEMBER)as BOUND;lia)
    INITIALIZED_SCOPE(proj1 INITIALIZED_READY)MAXIMUM ltac:(rewrite BYTES,SPLIT;reflexivity)eq_refl(eq_sym CHUNK_LENGTH)ltac:(unfold width;lia)CHUNK_DIGITS
    ltac:(rewrite LOOP_BYTES;exact BUFFER)LOOP_INDEX ltac:(rewrite DIGIT_COUNT in LOOP_WIDTH;exact LOOP_WIDTH)LOOP_SIZE LOOP_BASE LOOP_VALUE LOOP_RUN NONNULL)
    as(iterated &first_result &first_offset &first_parameters &iteration_prefix &from_fold &first_memory &first_world &FIRST_WELL &FIRST_NEXT &FIRST_ENTRIES &FIRST_BASE
      &FIRST_CURRENT &FIRST_PART_FREE &FIRST_SCALED_FREE &FIRST_READY &FIRST_VALUE &FIRST_INDEX &FIRST_WIDTH &FIRST_BASE_PARAMETER &FIRST_SIZE &FIRST_BYTES
      &FIRST_NEGATIVE &FIRST_DIGITS &ITERATION_EVENTS &ITERATION_EMPTY &FIRST_PREFIX &FIRST_REST).
  change(0*1000000000+gateway_decimal_value chunk)with(gateway_decimal_value chunk)in FIRST_READY.
  assert(REMAINING_MULTIPLE:Z.of_nat(length remaining)mod 9=0).
  { unfold remaining;rewrite length_skipn,Nat2Z.inj_sub by lia;rewrite Z2Nat.id by lia.
    unfold width;apply gateway_number_remaining_multiple. }
  assert(FOLD_BYTES:bytes=(prefix_bytes++chunk)++remaining)by(rewrite BYTES,SPLIT,app_assoc;reflexivity).
  assert(FOLD_INDEX:Z.of_nat(length prefix_bytes)+width=Z.of_nat(length(prefix_bytes++chunk)))
    by(rewrite length_app,Nat2Z.inj_add,CHUNK_LENGTH;reflexivity).
  destruct(gateway_reference_actual_number_nine_fold backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
    projection invocation(S(gateway_reference_next ledger))base base_offset stable_tail held scalar slots stream_block stream_offset initial readonly original size object bytes
    iterated(S(S(gateway_reference_next initialized)))first_result first_offset(gateway_decimal_value chunk)first_parameters
    (Z.of_nat(length prefix_bytes)+width)(prefix_bytes++chunk)remaining first_memory first_world from_fold value after next
    FIRST_WELL FIRST_ENTRIES FIRST_BASE FIRST_PART_FREE FIRST_SCALED_FREE
    ltac:(intros captured MEMBER;pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger held world captured FORMED SCOPE MEMBER)as BOUND;
      rewrite INITIALIZED_NEXT;lia)(proj2 FIRST_READY)(proj1 FIRST_READY)MAXIMUM FOLD_BYTES FOLD_INDEX REMAINING_MULTIPLE REMAINING_DIGITS
    ltac:(rewrite FIRST_BYTES,LOOP_BYTES;exact BUFFER)FIRST_INDEX FIRST_WIDTH FIRST_SIZE FIRST_BASE_PARAMETER FIRST_VALUE FIRST_REST NONNULL)
    as(folded &fold_ticket &fold_result &fold_offset &fold_parameters &fold_prefix &sign_events &fold_memory &fold_world &FOLD_WELL &FOLD_NEXT &FOLD_ENTRIES
      &FOLD_BASE &FOLD_CURRENT &FOLD_PART_FREE &FOLD_SCALED_FREE &FOLD_READY &FOLD_VALUE &FOLD_POSITION &FOLD_WIDTH &FOLD_BASE_PARAMETER &FOLD_SIZE
      &FOLD_BUFFER &FOLD_NEGATIVE &FOLD_DIGITS &FOLD_EVENTS &FOLD_EMPTY &FOLD_PREFIX &FOLD_REST &FOLD_TICKET).
  assert(DECIMAL:gateway_number_fold(gateway_decimal_value chunk)remaining=gateway_decimal_value digits).
  { rewrite gateway_number_fold_exact,<-gateway_decimal_append,<-SPLIT;reflexivity. }
  rewrite DECIMAL in FOLD_READY.
  assert(FOLD_RESULT_FREE:gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries folded)=None).
  { rewrite FOLD_ENTRIES;unfold stable_tail;apply gateway_number_two_heads_vacant;
      [unfold number_current_owner;discriminate|unfold number_base_owner;discriminate|exact RESULT_FREE]. }
  assert(FOLD_SIGNED_FREE:gateway_reference_take(number_signed_owner invocation)(gateway_reference_entries folded)=None).
  { rewrite FOLD_ENTRIES;unfold stable_tail;apply gateway_number_two_heads_vacant;
      [unfold number_current_owner,number_signed_owner;discriminate|unfold number_base_owner,number_signed_owner;discriminate|exact SIGNED_FREE]. }
  destruct(gateway_reference_actual_number_sign backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
    projection negative invocation folded fold_ticket fold_result fold_offset(gateway_decimal_value digits)(S(gateway_reference_next ledger))base base_offset
    (gateway_reference_entries ledger)held fold_parameters scalar slots stream_block stream_offset initial readonly original size object bytes
    fold_memory fold_world sign_events value after next FOLD_WELL FOLD_ENTRIES FOLD_SIGNED_FREE FOLD_RESULT_FREE
    ltac:(intros captured MEMBER;pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger held world captured FORMED SCOPE MEMBER)as BOUND;
      rewrite INITIALIZED_NEXT in FOLD_TICKET;lia)(proj2 FOLD_READY)(proj1 FOLD_READY)FOLD_BASE_PARAMETER FOLD_VALUE
    ltac:(rewrite FOLD_NEGATIVE,FIRST_NEGATIVE,LOOP_NEGATIVE;exact NEGATIVE)FOLD_REST NONNULL)
    as(final &FINAL_WELL &FINAL_NEXT &FINAL_ENTRIES &FINAL_OWNED &FINAL_READY &FINAL_EMPTY).
  exists final,(if negative then gateway_reference_next folded else fold_ticket).
  split;[exact FINAL_WELL|]. split.
  - pose proof(proj1(Forall_forall _ _)(proj2(proj2 FOLD_WELL))_ FOLD_CURRENT)as TICKET_BOUND;cbn in TICKET_BOUND.
    rewrite INITIALIZED_NEXT in FOLD_TICKET;destruct negative;lia.
  - split;[exact FINAL_ENTRIES|]. split;[exact FINAL_OWNED|]. split;[exact FINAL_READY|].
    rewrite EVENTS,ITERATION_EVENTS,FOLD_EVENTS,!gateway_received_append,SETUP_EMPTY,ITERATION_EMPTY,FOLD_EMPTY,FINAL_EMPTY;reflexivity.
Qed.
