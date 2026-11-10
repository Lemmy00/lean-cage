(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The whole actual JSON-number helper validates the same owned
   bytes and connects its selected constructor to one retained typed caller result. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumberOwners GatewayReferenceNumberIntegerConstruction GatewayReferenceFloatConstruction
  GatewayValue GatewayIntegerMemory GatewayIntegerPrefix GatewayIntegerCanonical GatewayNumberLexicalFacts
  GatewayJsonNumberLexical GatewayJsonNumberLexicalSlices GatewayJsonNumberSourceConnection GatewayNumberConstruction
  GatewayScalarConstructorCalls GatewayScalarDecoding GatewayFramedRuntime GatewayPathEvents GatewayObjectEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_json_number {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    invocation ledger held scalar slots stream_block stream_offset initial readonly original size object bytes mode_symbol before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  (forall identifier,gateway_reference_take(gateway_reference_temporary invocation identifier)(gateway_reference_entries ledger)=None)->
  gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->Int64.unsigned size<=65536->
  Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall candidate position,gateway_scalar_mode_region mode_symbol candidate position->readonly candidate position)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_json_number)[Vptr object Ptrofs.zero;Vlong size]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final ticket description,
    gateway_json_number bytes /\gateway_scalar_semantics decimal_float 9 bytes description /\
    gateway_reference_ledger_well_formed final /\(gateway_reference_next ledger<=ticket)%nat /\
    gateway_reference_entries final=gateway_reference_entry ticket(gateway_reference_result invocation)value::gateway_reference_entries ledger /\
    gateway_reference_owns final(gateway_reference_result invocation)ticket value /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture ticket value description])scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros FORMED TEMP_FREE RESULT_FREE SCOPE INPUT MAXIMUM MODE_SYMBOL MODE MODE_REGION RUN NONNULL.
  pose proof INPUT as[[[STORAGE[COUNT LOAD]]TERMINATED]PRIVATE].
  assert(SIZE_VALUE:size=Int64.repr(Z.of_nat(length bytes)))by(rewrite COUNT,Int64.repr_unsigned;reflexivity).
  assert(BOUND:Z.of_nat(length bytes)<=65536)by lia.
  set(property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger held
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    ledger held scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  destruct(gateway_actual_json_number_constructor backend property object bytes before world events value after next CLOSED(conj INPUT SCOPE)BOUND
    ltac:(intros offset byte BYTE memory current[READY HOLD];
      destruct READY as[[[SPACE[NUMBER READ]]ZERO]NATIVE];eapply gateway_integer_byte_load with(bytes:=bytes);
      [exact BOUND|rewrite NUMBER;exact READ|exact BYTE])
    ltac:(rewrite<-SIZE_VALUE;exact RUN)NONNULL)
    as(parts &parameters &definition &selected_mode &prefix &suffix &called &caller &PARSED &JSON &INTEGER_BOUND &SELECTED_MODE &API &EVENTS &QUIET
      &PREFIX &CALLED &BYTES_PARAMETER &SIZE_PARAMETER &INDEX_PARAMETER &END_PARAMETER &DIGITS_PARAMETER &NEGATIVE_PARAMETER &SIGN &REST).
  set(integer:=gateway_integer_start bytes+Z.of_nat(length(json_parts_integer parts)))in *.
  set(count:=Z.of_nat(length bytes))in *.
  assert(SELECTED_SAME:selected_mode=mode_symbol)by(rewrite MODE_SYMBOL in SELECTED_MODE;congruence);subst selected_mode.
  destruct(Z.eqb integer count)eqn:KIND.
  - unfold json_number_selected_api,json_number_selected_arguments,json_number_selected_cont in API,REST;rewrite KIND in API,REST.
    assert(INTEGER_END:integer=count)by(apply Z.eqb_eq;exact KIND).
    destruct(gateway_number_lexical_integer bytes parts PARSED SIGN INTEGER_END)as[INTEGER_BYTES INTEGER_GRAMMAR].
    destruct(gateway_number_integer_part_digits _ INTEGER_GRAMMAR)as[DIGITS_NONEMPTY DIGITS_ASCII].
    destruct(gateway_reference_actual_integer_construction backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
      projection(gateway_integer_negative bytes)invocation ledger held definition parameters(json_number_sign_prefix bytes)(json_parts_integer parts)
      scalar slots stream_block stream_offset initial readonly original size object bytes called caller suffix value after next FORMED
      (TEMP_FREE _value__1)(TEMP_FREE _base)(TEMP_FREE _part)(TEMP_FREE _scaled)(TEMP_FREE _signed_value)RESULT_FREE(proj2 CALLED)API(proj1 CALLED)MAXIMUM
      INTEGER_BYTES DIGITS_NONEMPTY DIGITS_ASCII BYTES_PARAMETER ltac:(rewrite SIZE_VALUE;exact SIZE_PARAMETER)
      ltac:(rewrite<-(proj2(json_number_unsigned_source bytes));exact DIGITS_PARAMETER)NEGATIVE_PARAMETER REST NONNULL)
      as(final &ticket &WELL &TICKET_BOUND &ENTRIES &OWNED &FINAL &EMPTY).
    exists final,ticket,(gateway_long_object(if gateway_integer_negative bytes then -gateway_decimal_value(json_parts_integer parts)
      else gateway_decimal_value(json_parts_integer parts))).
    split;[exact JSON|]. split;[eapply gateway_number_lexical_integer_semantics;[exact PARSED|exact SIGN|exact INTEGER_END]|].
    split;[exact WELL|]. split;[exact TICKET_BOUND|]. split;[exact ENTRIES|]. split;[exact OWNED|]. split;[exact FINAL|].
    rewrite EVENTS,gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),EMPTY;reflexivity.
  - unfold json_number_selected_api,json_number_selected_arguments,json_number_selected_cont in API,REST;rewrite KIND in API,REST.
    assert(FLOAT_END:integer<>count)by(apply Z.eqb_neq;exact KIND).
    assert(MARKER:gateway_json_float_marker bytes)by(eapply gateway_number_lexical_float;[exact PARSED|exact SIGN|exact FLOAT_END]).
    destruct(gateway_reference_actual_float_construction backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
      projection ledger(gateway_reference_temporary invocation _text)(gateway_reference_result invocation)held parameters definition
      scalar slots stream_block stream_offset initial readonly original size object bytes mode_symbol called caller suffix value after next
      FORMED(TEMP_FREE _text)RESULT_FREE ltac:(discriminate)(proj2 CALLED)API(proj1 CALLED)MAXIMUM MODE MODE_REGION
      ltac:(rewrite SIZE_VALUE;exact REST)NONNULL)
      as(final &characters &floating &TEXT &DECIMAL &WELL &OWNED &ENTRIES &NEXT &FINAL &EMPTY).
    exists final,(S(gateway_reference_next ledger)),(gateway_float_object floating).
    split;[exact JSON|]. split;[apply gateway_scalar_json_float with(characters:=characters);assumption|].
    split;[exact WELL|]. split;[lia|]. split;[exact ENTRIES|]. split;[exact OWNED|]. split;[exact FINAL|].
    rewrite EVENTS,gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),EMPTY;reflexivity.
Qed.
