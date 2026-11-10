(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An actual dictionary call composes its tag/count reads, allocation
   and strictly shorter recursive source executions into one source-owned result. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValue GatewayContainerABI GatewayReferenceValueProperties GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueActual GatewayValueNodeMemory GatewayValueTag GatewayStreamMemory
  GatewayContainerLength GatewayContainerCount GatewayContainerGuards GatewayContainerMemory GatewayReferenceEmptyContainer GatewayReferenceOwnedEmpty GatewayReferenceNormalForm GatewayReferenceDictionaryStart GatewayReferenceDictionaryFold GatewayObjectInstances GatewayReferenceParserInputs GatewayReferenceParseResult GatewayReferenceAncestors GatewayContainerEncoding GatewayScalarDecoding GatewayWordValues
  GatewayReferenceContainerAllocation GatewayReferenceContainerScope GatewayNativeRegions GatewayRegionThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceStackBound GatewayReferenceThreads GatewayThreadInvariant
  GatewayWordValues GatewayPathEvents GatewayObjectEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_parse_dictionary {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
    (references:gateway_reference_runtime backend python objects)
    (instances:gateway_instance_runtime backend(Clight.globalenv prog)python objects(fun _ _ _=>Logic.False))
    (projection:gateway_direct_io_projection backend io)
    mode_symbol run_limit(children:gateway_reference_short_parser backend python objects decimal_float detached io stable mode_symbol run_limit)
    context ledger held arguments stream_block stream_offset initial readonly original byte before world events value after next:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_scope python objects decimal_float ledger held world->gateway_reference_graphs_only held->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  Byte.unsigned byte=8->gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  gateway_received_bytes io(stream_descriptor initial)events=byte::tl(gateway_received_bytes io(stream_descriptor initial)events)->
  (length events<=run_limit)%nat->
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros CALL FORMED STACK SCOPE GRAPHS MODE MODE_SUBSET TAG STREAM INPUT READONLY RUN NONNULL OBSERVED LIMIT.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    reference_threads ledger held runtime)as SCOPED_THREADS.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPED_THREADS readonly)as THREADS.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { destruct INPUT as[SIDE[NATIVE[STABLE[RAW FRAME]]]];intros candidate position READ;split;
      [eapply gateway_value_readonly_live;[exact RAW|exact READ]|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { destruct INPUT as[SIDE REST];split;[split;[split;[exact SIDE|exact SCOPE]|exact OWNED]|exact REST]. }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno THREADS arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM AUGMENTED RUN NONNULL)
    as(slots &selected &tag_prefix &tag_read &tag_suffix &tag_before &tag_world &tag_after &tag_next &tag_stream &
      EVENTS &DEPTH &NODES &TAG_QUIET &TAG_PREFIX &ALLOCATED &TAG_RUN &TAG_OBSERVED &TAG_LOAD &TAG_STREAM &TAG_ACTIVE &TAG_REST).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),TAG_OBSERVED in OBSERVED.
    inversion OBSERVED;reflexivity. }
  subst selected;rewrite TAG in TAG_LOAD.
  destruct(gateway_actual_container_count backend io native stable augmented thread_errno THREADS gateway_container_object slots arguments initial
    stream_block stream_offset tag_stream readonly original tag_after tag_next tag_suffix value after next STREAM(conj TAG_ACTIVE TAG_LOAD)TAG_REST NONNULL)
    as(parameters &count_bytes &count_prefix &count_read &count_suffix &count_before &count_world &count_after &count_next &count_stream &
      COUNT_EVENTS &COUNT_QUIET &COUNT_STREAM_PARAMETER &COUNT_DEPTH &COUNT_PREFIX &COUNT_RUN &COUNT_OBSERVED &COUNT_LENGTH &COUNT_LOAD &COUNT_STREAM &COUNT_ACTIVE &COUNT_REST).
  set(size:=Int64.repr(gateway_decoded_value count_bytes)).
  assert(WIDTH:length count_bytes=4%nat)by(change(Z.of_nat(length count_bytes)=4)in COUNT_LENGTH;lia).
  assert(COUNTED:gateway_container_counted native stable base gateway_container_object slots stream_block stream_offset count_stream readonly original
    size count_after count_next).
  { eapply gateway_container_counted_rebase;[exact(conj COUNT_ACTIVE COUNT_LOAD)|].
    pose proof(proj1(proj1(proj1 COUNT_ACTIVE)))as[[SIDE HELD]REGION];exact SIDE. }
  pose proof(proj1(proj1(proj1 COUNT_ACTIVE)))as[[SIDE HELD]REGION].
  destruct(gateway_reference_actual_dictionary_start backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads constructors projection context ledger held slots arguments parameters stream_block stream_offset count_stream readonly original size
    count_after count_next count_suffix value after next FORMED STACK HELD GRAPHS STREAM COUNT_STREAM_PARAMETER COUNTED
    ltac:(intros candidate position READ;exact(proj2(REGION candidate position READ)))COUNT_REST NONNULL)
    as(minted &parent &offset &parent_snapshot &loop_parameters &prefix &loop_events &loop_memory &loop_world &START_EVENTS &EMPTY_PREFIX &MINT &MINT_WELL &
      MINT_ENTRIES &PARENT_LOOKUP &SNAPSHOTS &EXCLUDED &PARENT &LOOP_STREAM &LOOP_DEPTH &LOOP_INDEX &TO_LOOP &LOOP_READY &LOOP_RUN).
  assert(LOOP_LIMIT:(length loop_events<=run_limit)%nat).
  { rewrite EVENTS,COUNT_EVENTS,START_EVENTS,!length_app in LIMIT;lia. }
  destruct(gateway_reference_actual_dictionary_fold backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads containers abi references instances projection mode_symbol run_limit children context ledger minted held(gateway_reference_next ledger)
    parent offset[][]parent_snapshot slots loop_parameters(gateway_value_depth arguments)Int64.zero size stream_block stream_offset count_stream readonly original
    loop_memory loop_world loop_events value after next CALL STACK MINT_WELL MINT_ENTRIES ltac:(apply Nat.le_refl)GRAPHS SNAPSHOTS
    PARENT_LOOKUP ltac:(constructor)ltac:(intros pointer MEMBER;inversion MEMBER)EXCLUDED PARENT
    ltac:(rewrite LOOP_STREAM,STREAM;reflexivity)ltac:(rewrite LOOP_DEPTH;exact COUNT_DEPTH)LOOP_INDEX eq_refl
    ltac:(apply Int64.unsigned_range_2)MODE MODE_SUBSET LOOP_READY LOOP_RUN NONNULL LOOP_LIMIT)
    as(final &final_stream &remaining &chunks &DECODED &FINAL_CONTEXT &FINAL_NATIVE &FINAL_DESCRIPTOR &COUNT &FRAMES &BYTES).
  assert(TAG_DESCRIPTOR:stream_descriptor tag_stream=stream_descriptor initial)by(exact(proj1 TAG_STREAM)).
  assert(COUNT_DESCRIPTOR:stream_descriptor count_stream=stream_descriptor initial)by(rewrite(proj1 COUNT_STREAM);exact TAG_DESCRIPTOR).
  assert(SIZE:gateway_decoded_value count_bytes=Z.of_nat(length remaining)).
  { change(length remaining=Z.to_nat(Int64.unsigned size))in COUNT.
    rewrite COUNT,Z2Nat.id by(apply Int64.unsigned_range_2).
    unfold size;rewrite gateway_decoded_unsigned by lia;reflexivity. }
  assert(EXACT_BYTES:gateway_received_bytes io(stream_descriptor initial)events=byte::(count_bytes++concat chunks)).
  { rewrite EVENTS,COUNT_EVENTS,START_EVENTS,!gateway_received_append,
      (gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),TAG_OBSERVED,
      (gateway_quiet_received io(stream_descriptor initial)count_prefix COUNT_QUIET),<-TAG_DESCRIPTOR,COUNT_OBSERVED,TAG_DESCRIPTOR,
      (EMPTY_PREFIX(stream_descriptor initial)),<-COUNT_DESCRIPTOR,BYTES;reflexivity. }
  exists final,final_stream,(LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields remaining)),(gateway_reference_next ledger).
  split;[exact DECODED|]. split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;
    [rewrite FINAL_DESCRIPTOR;exact COUNT_DESCRIPTOR|].
  rewrite EXACT_BYTES;apply gateway_object_source_framing;[exact TAG|exact WIDTH|exact SIZE|].
  apply gateway_field_segments_framed;exact FRAMES.
Qed.
