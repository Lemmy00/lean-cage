(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Repeated actual nine-digit iterations consume the remaining
   payload and preserve the same source-owned operands, native storage and reference tail. *)
From Stdlib Require Import ZArith List Lia Arith.Wf_nat.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceAncestors
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumberOwners GatewayReferenceNumberIteration GatewayReferenceNumberPart
  GatewayNumber GatewayNumberFoldMath GatewayNumberIntegerLoopSource GatewayNumberIntegerStructure GatewayContexts GatewaySourceSegments
  GatewayScalarConstructorCalls GatewayScalarLength GatewayValueEntry GatewayFramedRuntime GatewayPathEvents GatewayObjectEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section NineFold.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)(decimal_float:list Z->Floats.float->Prop)
  (detached:Values.val->mem->World->Prop)(io:Event->option gateway_native_io)(stable:World->block->Z->Prop)
  (thread_errno:World->int)(heap_allocation:block->Z->Prop).
Let native:=fun current object=>gateway_native_private(python current)object.
Let base_discipline:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base_discipline thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)(references:gateway_reference_runtime backend python objects)
  (reference_threads:gateway_reference_thread_contract backend native stable base_discipline heap_allocation python objects)
  (projection:gateway_direct_io_projection backend io).
Context(invocation:nat)(base_ticket:nat)(base:block)(base_offset:ptrofs)(tail:list gateway_owned_reference)(held:list gateway_held_value)
  (scalar:gateway_scalar_case)(slots:gateway_value_slots)(stream_block:block)(stream_offset:ptrofs)(initial:gateway_stream_values)
  (readonly:block->Z->Prop)(original:mem)(size:int64)(object:block)(bytes:list Byte.int).

Theorem gateway_reference_actual_number_nine_fold ledger current_ticket current current_offset accumulator parameters index prefix_bytes remaining
    before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry current_ticket(number_current_owner invocation)(Vptr current current_offset)::tail->
  gateway_reference_owns ledger(number_base_owner invocation)base_ticket(Vptr base base_offset)->
  gateway_reference_take(number_part_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(number_scaled_owner invocation)(gateway_reference_entries ledger)=None->
  (forall captured,In captured held->gateway_held_ticket captured<>current_ticket)->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000);
      gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object accumulator)])world->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->Int64.unsigned size<=65536->
  bytes=prefix_bytes++remaining->index=Z.of_nat(length prefix_bytes)->Z.of_nat(length remaining)mod 9=0->
  Forall(fun byte=>48<=Byte.unsigned byte<=57)remaining->
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!_index=Some(Vlong(Int64.repr index))->
  parameters!_width=Some(Vlong(Int64.repr 9))->parameters!_size=Some(Vlong size)->
  parameters!_base=Some(Vptr base base_offset)->parameters!_value__1=Some(Vptr current current_offset)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final ticket result result_offset final_parameters prefix suffix done_memory done_world,
    gateway_reference_ledger_well_formed final /\(gateway_reference_next ledger<=gateway_reference_next final)%nat /\
    gateway_reference_entries final=gateway_reference_entry ticket(number_current_owner invocation)(Vptr result result_offset)::tail /\
    gateway_reference_owns final(number_base_owner invocation)base_ticket(Vptr base base_offset) /\
    gateway_reference_owns final(number_current_owner invocation)ticket(Vptr result result_offset) /\
    gateway_reference_take(number_part_owner invocation)(gateway_reference_entries final)=None /\
    gateway_reference_take(number_scaled_owner invocation)(gateway_reference_entries final)=None /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000);
        gateway_reference_scalar_capture ticket(Vptr result result_offset)(gateway_long_object(gateway_number_fold accumulator remaining))])
      scalar slots stream_block stream_offset initial readonly original size object bytes done_memory done_world /\
    final_parameters!_value__1=Some(Vptr result result_offset) /\final_parameters!_index=Some(Vlong size) /\
    final_parameters!_width=Some(Vlong(Int64.repr 9)) /\final_parameters!_base=Some(Vptr base base_offset) /\
    final_parameters!_size=Some(Vlong size) /\final_parameters!_bytes=parameters!_bytes /\
    final_parameters!_negative=parameters!_negative /\final_parameters!_digits=parameters!_digits /\
    events=prefix++suffix /\gateway_received_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env parameters before)world)prefix
      (gateway_live(State f_host_json_number Sskip number_integer_loop_cont empty_env final_parameters done_memory)done_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_json_number Sskip number_integer_loop_cont empty_env final_parameters done_memory)done_world)suffix
      (gateway_live(Returnstate value Kstop after)next) /\(current_ticket<=ticket)%nat.
Proof.
  remember(length remaining)as measure eqn:MEASURE.
  revert ledger current_ticket current current_offset accumulator parameters index prefix_bytes remaining before world events MEASURE.
  induction measure using lt_wf_ind;intros ledger current_ticket current current_offset accumulator parameters index prefix_bytes remaining before world events MEASURE
    FORMED ENTRIES BASE_OWNED PART_FREE SCALED_FREE DIFFERENT SCOPE INPUT MAXIMUM BYTES POSITION MULTIPLE DIGITS BUFFER INDEX WIDTH SIZE BASE_PARAMETER CURRENT RUN NONNULL.
  rewrite MEASURE in MULTIPLE.
  assert(CURRENT_OWNED:gateway_reference_owns ledger(number_current_owner invocation)current_ticket(Vptr current current_offset))
    by(unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity).
  destruct remaining as[|first rest]eqn:REMAINING.
  - pose proof INPUT as[[[STORAGE[COUNT LOAD]]TERMINATED]PRIVATE].
    assert(EXHAUSTED:index=Int64.unsigned size)by(rewrite BYTES,app_nil_r in COUNT;lia).
    set(base_capture:=gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000)).
    set(current_capture:=gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object accumulator)).
    set(property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger(held++[base_capture;current_capture])
      scalar slots stream_block stream_offset initial readonly original size object bytes).
    pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
      ledger(held++[base_capture;current_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
    pose proof(gateway_number_integer_loop_exit backend(Clight.globalenv prog)property parameters size before CLOSED
      ltac:(rewrite EXHAUSTED,Int64.repr_unsigned in INDEX;exact INDEX)SIZE)as EXIT.
    destruct(gateway_source_segment_cut backend(Clight.globalenv prog)_ _ _ _ EXIT before world events value after next(conj INPUT SCOPE)RUN)
      as(prefix &suffix &done_memory &done_world &EVENTS &QUIET &PREFIX &READY &REST).
    exists ledger,current_ticket,current,current_offset,parameters,prefix,suffix,done_memory,done_world.
    split;[exact FORMED|]. split;[lia|]. split;[exact ENTRIES|]. split;[exact BASE_OWNED|]. split;[exact CURRENT_OWNED|].
    split;[exact PART_FREE|]. split;[exact SCALED_FREE|]. split;[exact READY|]. split;[exact CURRENT|]. split.
    + rewrite EXHAUSTED,Int64.repr_unsigned in INDEX;exact INDEX.
    + split;[exact WIDTH|]. split;[exact BASE_PARAMETER|]. split;[exact SIZE|]. split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|].
      split;[exact EVENTS|]. split;[exact(gateway_quiet_received io(stream_descriptor initial)prefix QUIET)|].
      split;[exact PREFIX|]. split;[exact REST|lia].
  - assert(NINE:(9<=length(first::rest))%nat)by(apply gateway_number_nine_available;[discriminate|exact MULTIPLE]).
    set(chunk:=firstn 9(first::rest));set(remaining_digits:=skipn 9(first::rest)).
    assert(SPLIT:first::rest=chunk++remaining_digits)by(symmetry;apply firstn_skipn).
    assert(CHUNK_LENGTH:length chunk=9%nat)by(unfold chunk;rewrite length_firstn,Nat.min_l by lia;reflexivity).
    pose proof DIGITS as ALL_DIGITS;rewrite SPLIT in ALL_DIGITS;apply Forall_app in ALL_DIGITS;destruct ALL_DIGITS as[CHUNK_DIGITS REST_DIGITS].
    assert(TAKE:gateway_reference_take(number_current_owner invocation)(gateway_reference_entries ledger)=
      Some(gateway_reference_entry current_ticket(number_current_owner invocation)(Vptr current current_offset),tail)).
    { rewrite ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner];
      destruct(gateway_reference_place_eq(number_current_owner invocation)(number_current_owner invocation));[reflexivity|congruence]. }
    destruct(gateway_reference_actual_number_iteration backend python objects decimal_float detached io stable thread_errno heap_allocation
      runtime constructors references reference_threads projection invocation ledger base_ticket base base_offset current_ticket current current_offset accumulator tail held
      parameters index 9 prefix_bytes chunk remaining_digits scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next
      FORMED BASE_OWNED CURRENT_OWNED TAKE PART_FREE SCALED_FREE DIFFERENT SCOPE INPUT MAXIMUM
      ltac:(rewrite BYTES,SPLIT;reflexivity)POSITION ltac:(rewrite CHUNK_LENGTH;reflexivity)ltac:(lia)CHUNK_DIGITS BUFFER INDEX WIDTH SIZE BASE_PARAMETER CURRENT RUN NONNULL)
      as(iterated &result &result_offset &loop_parameters &iteration_prefix &loop_events &loop_memory &loop_world &ITERATED_WELL &ITERATED_NEXT &ITERATED_ENTRIES
        &ITERATED_BASE &ITERATED_CURRENT &ITERATED_PART &ITERATED_SCALED &ITERATED_READY &LOOP_VALUE &LOOP_INDEX &LOOP_WIDTH &LOOP_BASE &LOOP_SIZE &LOOP_BYTES
        &LOOP_NEGATIVE &LOOP_DIGITS &EVENTS &ITERATION_EMPTY &TO_LOOP &LOOP_REST).
    assert(SHORT:(length remaining_digits<measure)%nat).
    { unfold remaining_digits;rewrite length_skipn,MEASURE;apply Nat.sub_lt;[exact NINE|lia]. }
    assert(NEXT_BYTES:bytes=(prefix_bytes++chunk)++remaining_digits).
    { rewrite BYTES,SPLIT,app_assoc;reflexivity. }
    assert(NEXT_INDEX:index+9=Z.of_nat(length(prefix_bytes++chunk))).
    { rewrite length_app,Nat2Z.inj_add,CHUNK_LENGTH;cbn;lia. }
    assert(NEXT_MULTIPLE:Z.of_nat(length remaining_digits)mod 9=0).
    { apply gateway_number_skip_nine_multiple;[exact NINE|exact MULTIPLE]. }
    assert(NEXT_DIFFERENT:forall captured,In captured held->gateway_held_ticket captured<>S(S(gateway_reference_next ledger))).
    { intros captured MEMBER SAME.
      pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger
        (held++[gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000);
          gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object accumulator)])world captured FORMED SCOPE
        ltac:(apply in_or_app;left;exact MEMBER))as BOUND;lia. }
    destruct(H(length remaining_digits)SHORT iterated(S(S(gateway_reference_next ledger)))result result_offset
      (accumulator*1000000000+gateway_decimal_value chunk)loop_parameters(index+9)(prefix_bytes++chunk)remaining_digits loop_memory loop_world loop_events eq_refl
      ITERATED_WELL ITERATED_ENTRIES ITERATED_BASE ITERATED_PART ITERATED_SCALED NEXT_DIFFERENT(proj2 ITERATED_READY)(proj1 ITERATED_READY)MAXIMUM
      NEXT_BYTES NEXT_INDEX NEXT_MULTIPLE REST_DIGITS ltac:(rewrite LOOP_BYTES;exact BUFFER)LOOP_INDEX LOOP_WIDTH LOOP_SIZE LOOP_BASE LOOP_VALUE LOOP_REST NONNULL)
      as(final &ticket &final_result &final_offset &final_parameters &recursive_prefix &suffix &done_memory &done_world &FINAL_WELL &FINAL_NEXT &FINAL_ENTRIES
        &FINAL_BASE &FINAL_CURRENT &FINAL_PART &FINAL_SCALED &FINAL_READY &FINAL_VALUE &FINAL_INDEX &FINAL_WIDTH &FINAL_BASE_PARAMETER &FINAL_SIZE
        &FINAL_BYTES &FINAL_NEGATIVE &FINAL_DIGITS &RECURSIVE_EVENTS &RECURSIVE_EMPTY &RECURSIVE_PREFIX &FINAL_REST &FINAL_TICKET).
    assert(ARITHMETIC:gateway_number_fold accumulator(first::rest)=
      gateway_number_fold(accumulator*1000000000+gateway_decimal_value chunk)remaining_digits).
    { rewrite SPLIT;apply gateway_number_nine_fold;exact CHUNK_LENGTH. }
    rewrite<-ARITHMETIC in FINAL_READY.
    exists final,ticket,final_result,final_offset,final_parameters,(iteration_prefix++recursive_prefix),suffix,done_memory,done_world.
    split;[exact FINAL_WELL|]. split;[lia|]. split;[exact FINAL_ENTRIES|]. split;[exact FINAL_BASE|]. split;[exact FINAL_CURRENT|].
    split;[exact FINAL_PART|]. split;[exact FINAL_SCALED|]. split;[exact FINAL_READY|].
    split;[exact FINAL_VALUE|]. split;[exact FINAL_INDEX|]. split;[exact FINAL_WIDTH|]. split;[exact FINAL_BASE_PARAMETER|]. split;[exact FINAL_SIZE|].
    split;[rewrite FINAL_BYTES,LOOP_BYTES;reflexivity|]. split;[rewrite FINAL_NEGATIVE,LOOP_NEGATIVE;reflexivity|].
    split;[rewrite FINAL_DIGITS,LOOP_DIGITS;reflexivity|]. split;[rewrite EVENTS,RECURSIVE_EVENTS,app_assoc;reflexivity|]. split.
    + rewrite gateway_received_append,ITERATION_EMPTY,RECURSIVE_EMPTY;reflexivity.
    + split;[eapply gateway_steps_append;[exact TO_LOOP|exact RECURSIVE_PREFIX]|]. split;[exact FINAL_REST|].
      pose proof(proj1(Forall_forall _ _)(proj2(proj2 FORMED))_ CURRENT_OWNED)as CURRENT_BOUND;cbn in CURRENT_BOUND;lia.
Qed.
End NineFold.
