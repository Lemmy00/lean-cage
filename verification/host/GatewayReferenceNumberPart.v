(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An iteration's part constructor consumes the exact contiguous
   initialized payload slice computed by its actual digit loop. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNumericContext GatewayReferenceNumericRequests
  GatewayReferenceNumberLiterals GatewayReferenceEmptyContainer GatewayNumber GatewayNumberChunkSource GatewayNumberChunkReceipt GatewayNumberIntegerLoopSource
  GatewayNumberIntegerStructure GatewayNumberConstruction GatewayNumberIterationFailure GatewayContexts GatewaySourcePaths GatewaySourceSegments
  GatewayScalarConstructorCalls GatewayScalarTerminate GatewayFramedRuntime GatewayPathEvents GatewayObjectRuns GatewayObjectEvents GatewayStreamInterface GatewayThreadRuntime GatewayIntegerScan.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_part {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    ledger owner held parameters index width prefix_bytes chunk suffix_bytes scalar slots stream_block stream_offset initial readonly original size object bytes
    before world events value after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->Int64.unsigned size<=65536->
  bytes=prefix_bytes++chunk++suffix_bytes->index=Z.of_nat(length prefix_bytes)->width=Z.of_nat(length chunk)->0<width<=9->
  Forall(fun byte=>48<=Byte.unsigned byte<=57)chunk->
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!_index=Some(Vlong(Int64.repr index))->
  parameters!_width=Some(Vlong(Int64.repr width))->parameters!_size=Some(Vlong size)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final part part_offset called_parameters prefix suffix part_after part_next,
    gateway_reference_apply(gateway_reference_mint owner(Vptr part part_offset))(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)(Vptr part part_offset) /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)(Vptr part part_offset)(gateway_long_object(gateway_decimal_value chunk))])
      scalar slots stream_block stream_offset initial readonly original size object bytes part_after part_next /\
    (forall identifier,identifier<>_chunk->identifier<>_offset->identifier<>_t'23->called_parameters!identifier=parameters!identifier) /\
    events=prefix++suffix /\gateway_received_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env parameters before)world)prefix
      (gateway_live(Returnstate(Vptr part part_offset)(number_integer_part_cont called_parameters)part_after)part_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vptr part part_offset)(number_integer_part_cont called_parameters)part_after)part_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros FORMED VACANT SCOPE INPUT MAXIMUM BYTES POSITION WIDTH WIDTH_BOUND DIGITS BUFFER INDEX LIMIT SIZE RUN NONNULL.
  pose proof INPUT as[[[STORAGE[COUNT LOAD]]TERMINATED]PRIVATE].
  assert(BOUND:Z.of_nat(length bytes)<=65536)by lia.
  assert(LESS:0<=index<Int64.unsigned size).
  { rewrite BYTES,!length_app in COUNT;rewrite!Nat2Z.inj_add in COUNT;lia. }
  set(property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger held
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    ledger held scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  pose proof(gateway_number_integer_loop_enter backend(Clight.globalenv prog)property parameters index(Int64.unsigned size)before
    CLOSED LESS MAXIMUM INDEX ltac:(rewrite Int64.repr_unsigned;exact SIZE))as ENTER.
  set(entered:=PTree.set _offset(Vlong Int64.zero)(PTree.set _chunk(Vlong Int64.zero)parameters)).
  assert(ENTERED:gateway_number_chunk_state entered object Ptrofs.zero index width 0 0).
  { unfold gateway_number_chunk_state,entered;repeat split;
      repeat rewrite PTree.gso by discriminate;first[exact BUFFER|exact INDEX|exact LIMIT|apply PTree.gss]. }
  destruct(gateway_number_actual_chunk_segment backend(Clight.globalenv prog)property entered object bytes prefix_bytes chunk suffix_bytes index width before
    CLOSED BYTES BOUND POSITION WIDTH ltac:(lia)DIGITS ENTERED
    ltac:(intros memory current[READY HOLD];destruct READY as[[[SPACE[NUMBER READ]]ZERO]NATIVE];rewrite NUMBER;exact READ))
    as(chunk_parameters &CHUNK &CHUNK_STATE &CHUNK_PARAMETERS).
  pose proof(gateway_integer_segments_append backend(Clight.globalenv prog)_ _ _ _ _ _ ENTER CHUNK)as DIGIT_PATH.
  destruct gateway_actual_number_constructor_bindings as[_[definition[DEFINITION[BINDING TYPE]]]].
  destruct BINDING as[symbol[SYMBOL FUNCTION]].
  pose proof(gateway_number_chunk_part_source_path backend(Clight.globalenv prog)property chunk_parameters(Int64.repr(gateway_decimal_value chunk))before
    symbol definition CLOSED(proj2(proj2(proj2(proj2 CHUNK_STATE))))SYMBOL FUNCTION TYPE)as PART_PATH.
  pose proof(gateway_segment_then_call backend(Clight.globalenv prog)_ _ _ _ _ _ _ _ DIGIT_PATH PART_PATH)as PATH.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next(conj INPUT SCOPE)RUN)
    as(source_prefix &rest &part_before &part_world &EVENTS &SOURCE_QUIET &TO_PART &PART_READY &FROM_PART).
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vlong(Int64.repr(gateway_decimal_value chunk))](number_integer_part_cont chunk_parameters)
    part_before part_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_PART)
    as(constructing &suffix &part_value &part_after &part_next &PART_EVENTS &PART_RUN &PART_REST).
  assert(PART_NONNULL:part_value<>Vnullptr).
  { intro NULL;subst part_value;apply NONNULL;exact(gateway_number_null_part_denied backend(Clight.globalenv prog)chunk_parameters part_after
      part_after part_next suffix value after next PART_REST). }
  destruct(gateway_reference_actual_literal_storage backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime constructors reference_threads true ledger owner held definition(Int64.repr(gateway_decimal_value chunk))scalar slots stream_block stream_offset
    initial readonly original size object bytes part_before part_world constructing part_value part_after part_next FORMED VACANT(proj2 PART_READY)DEFINITION
    (proj1 PART_READY)PART_RUN PART_NONNULL)as(final &MINT &WELL &OWNED &PART_STORAGE &PART_SCOPE).
  assert(CHUNK_BOUND:0<=gateway_decimal_value chunk<1000000000).
  { apply gateway_nine_digit_chunk_fits;[lia|exact DIGITS]. }
  rewrite Int64.unsigned_repr in PART_SCOPE by(change Int64.max_unsigned with 18446744073709551615;lia).
  destruct(gateway_reference_owned_pointer python objects final owner(gateway_reference_next ledger)part_value part_after part_next
    ltac:(eapply gateway_scalar_private_side;exact PART_STORAGE)(proj1 PART_SCOPE)OWNED)
    as(part &part_offset &PART_POINTER &PART_VALID);subst part_value.
  pose proof(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(number_integer_part_cont chunk_parameters)ltac:(cbn;exact I)PART_RUN)as PART_CALLER.
  exists final,part,part_offset,chunk_parameters,(source_prefix++constructing),suffix,part_after,part_next.
  split;[exact MINT|]. split;[exact WELL|]. split;[exact OWNED|]. split;[split;[exact PART_STORAGE|exact PART_SCOPE]|]. split.
  - intros identifier A B C;rewrite CHUNK_PARAMETERS by assumption;unfold entered;repeat rewrite PTree.gso by congruence;reflexivity.
  - split;[rewrite EVENTS,PART_EVENTS,app_assoc;reflexivity|]. split.
    + rewrite gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)source_prefix SOURCE_QUIET).
      rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_long_unsigned definition
        [Vlong(Int64.repr(gateway_decimal_value chunk))]part_before part_world constructing(Vptr part part_offset)part_after part_next
        (stream_descriptor initial)projection DEFINITION PART_RUN);reflexivity.
    + split;[eapply gateway_steps_append;[exact TO_PART|exact PART_CALLER]|exact PART_REST].
Qed.
