(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A whole actual empty-array/object call retains the exact tag/count
   reads, real builtin allocation and source-owned final result. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueActual GatewayValueNodeMemory GatewayValueTag GatewayStreamMemory
  GatewayContainerLength GatewayContainerCount GatewayContainerGuards GatewayContainerMemory GatewayReferenceEmptyContainer GatewayReferenceOwnedEmpty GatewayReferenceNormalForm
  GatewayReferenceContainerAllocation GatewayReferenceContainerScope GatewayNativeRegions GatewayRegionThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceStackBound GatewayReferenceThreads GatewayThreadInvariant
  GatewayWordValues GatewayPathEvents GatewayObjectEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_equal_length_prefix {A}(first second tail:list A):
  length first=length second->first++tail=second->first=second /\tail=[].
Proof.
  intros SAME APPEND;assert(TAIL:length tail=0%nat)by(apply(f_equal (@length A))in APPEND;rewrite length_app in APPEND;lia).
  destruct tail;[rewrite app_nil_r in APPEND;auto|discriminate].
Qed.

Theorem gateway_reference_actual_empty_stream_value_owned {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (constructors:gateway_objects_runtime backend python objects decimal_float)(io_projection:gateway_direct_io_projection backend io)
    context ledger held container arguments stream_block stream_offset initial readonly original byte before world events value after next:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_scope python objects decimal_float ledger held world->Byte.unsigned byte=gateway_container_code container->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  gateway_received_bytes io(stream_descriptor initial)events=byte::repeat Byte.zero 4->
  exists final final_stream,
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_wire_capture(gateway_reference_next ledger)value(gateway_container_empty_wire container)])next /\
    gateway_value_heap decimal_float(objects next)value(gateway_container_empty_wire container) /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset final_stream readonly original after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    exists tag_stream,gateway_stream_read_after(gateway_stream_node_debit initial)1 tag_stream /\
      gateway_stream_read_after tag_stream 4 final_stream /\
    gateway_reference_result_entries context ledger final(gateway_reference_next ledger)value /\
    gateway_reference_source_bound(Clight.globalenv prog)(Returnstate value context after)final /\
    (forall captured,In captured held->gateway_held_object captured<>value).
Proof.
  intros CALL FORMED STACK SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    references ledger held runtime)as SCOPED_THREADS.
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
  destruct(gateway_actual_container_count backend io native stable augmented thread_errno THREADS container slots arguments initial
    stream_block stream_offset tag_stream readonly original tag_after tag_next tag_suffix value after next STREAM(conj TAG_ACTIVE TAG_LOAD)TAG_REST NONNULL)
    as(parameters &count_bytes &count_prefix &count_read &count_suffix &count_before &count_world &count_after &count_next &count_stream &
      COUNT_EVENTS &COUNT_QUIET &COUNT_STREAM_PARAMETER &COUNT_DEPTH &COUNT_PREFIX &COUNT_RUN &COUNT_OBSERVED &COUNT_LENGTH &COUNT_LOAD &COUNT_STREAM &COUNT_ACTIVE &COUNT_REST).
  assert(TAG_DESCRIPTOR:stream_descriptor tag_stream=stream_descriptor initial)by(exact(proj1 TAG_STREAM)).
  assert(COUNT_BYTES:count_bytes=repeat Byte.zero 4).
  { rewrite EVENTS,COUNT_EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),
      TAG_OBSERVED,(gateway_quiet_received io(stream_descriptor initial)count_prefix COUNT_QUIET),<-TAG_DESCRIPTOR,COUNT_OBSERVED in OBSERVED.
    injection OBSERVED as TAIL.
    assert(LENGTH:length count_bytes=length(repeat Byte.zero 4)).
    { rewrite repeat_length;change(Z.of_nat(length count_bytes)=4)in COUNT_LENGTH;lia. }
    exact(proj1(gateway_equal_length_prefix count_bytes(repeat Byte.zero 4)
      (gateway_received_bytes io(stream_descriptor tag_stream)count_suffix)LENGTH TAIL)). }
  assert(ZERO:gateway_decoded_value(repeat Byte.zero 4)=0)by reflexivity.
  rewrite COUNT_BYTES,ZERO in COUNT_LOAD;change(Mem.loadv Mint64 count_after(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong Int64.zero))in COUNT_LOAD.
  assert(COUNTED:gateway_container_counted native stable base container slots stream_block stream_offset count_stream readonly original
    Int64.zero count_after count_next).
  { eapply gateway_container_counted_rebase;[exact(conj COUNT_ACTIVE COUNT_LOAD)|].
    pose proof(proj1(proj1(proj1 COUNT_ACTIVE)))as[[SIDE HELD]REGION];exact SIDE. }
  pose proof(proj1(proj1(proj1 COUNT_ACTIVE)))as[[SIDE HELD]REGION].
  destruct(gateway_reference_actual_empty_container_entries backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime references constructors io_projection context ledger held container slots arguments parameters stream_block stream_offset count_stream
    readonly original count_after count_next count_suffix value after next CALL FORMED STACK HELD STREAM COUNT_STREAM_PARAMETER COUNTED
    ltac:(intros candidate position READ;exact(proj2(REGION candidate position READ)))COUNT_REST NONNULL)
    as(final &WELL &RESULT &BINDING &FINAL_SCOPE &HEAP &FINAL_CONTEXT &FINAL_NATIVE &FINAL_EMPTY &FRESH &ENTRIES &FINAL_BOUND).
  exists final,count_stream;split;[exact WELL|]. split;[exact RESULT|]. split;[exact BINDING|]. split;[exact FINAL_SCOPE|].
  split;[exact HEAP|]. split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. exists tag_stream;split.
  -
  change(gateway_stream_read_after(gateway_stream_node_debit initial)1 tag_stream).
  change(gateway_stream_read_after(gateway_stream_node_debit initial)(Int.unsigned(Int.repr 1))tag_stream)in TAG_STREAM;exact TAG_STREAM.
  - split;[exact COUNT_STREAM|]. split;[exact ENTRIES|]. split;assumption.
Qed.
