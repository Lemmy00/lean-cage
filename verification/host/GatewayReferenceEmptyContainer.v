(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real zero-count container path allocates and returns its exact
   empty builtin with a source-owned result and the same checked stream. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayImport GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueRegions
  GatewayContainerLength GatewayContainerGuards GatewayContainerAllocation GatewayContainerCalls GatewayContainerSetup
  GatewayContainerSetupReceipt GatewayContainerMemory GatewayContainerLoopSource GatewayReferenceLedger GatewayReferencePlaces
  GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceActivation GatewayReferenceStackBound GatewayReferenceContainerScope
  GatewayReferenceContainerAllocation GatewayReferenceContainerContext GatewayReferenceContainerExit GatewayRegionThreads GatewayNativeRegions
  GatewayThreadInvariant GatewayPathEvents GatewayObjectEvents GatewayObjectRuns GatewayStreamLayout GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_container_counted_rebase {World}native stable discipline replacement container slots stream_block stream_offset initial readonly original size
    memory world:
  @gateway_container_counted World native stable discipline container slots stream_block stream_offset initial readonly original size memory world->
  replacement None memory world->gateway_container_counted native stable replacement container slots stream_block stream_offset initial readonly original size memory world.
Proof.
  intros[[[[SIDE[STREAM[STABLE[INPUT FRAME]]]]SLOTS]TAG]SIZE]NEXT_SIDE.
  split;[split;[split;[|exact SLOTS]|exact TAG]|exact SIZE].
  split;[exact NEXT_SIDE|]. split;[exact STREAM|]. split;[exact STABLE|]. split;assumption.
Qed.

Lemma gateway_reference_owned_pointer {World}(python:World->python_world)(objects:World->gateway_object_heap)ledger owner ticket value memory world:
  gateway_objects_ready(python world)(objects world)memory->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger owner ticket value->exists block offset,value=Vptr block offset /\
    Mem.weak_valid_pointer memory block(Ptrofs.unsigned offset)=true.
Proof.
  intros READY FIT OWNED.
  assert(ROOT:gateway_rooted(python world)(objects world)value)by(eapply gateway_reference_owned_rooted;eassumption).
  destruct READY as[[_[_[_[_ POINTERS]]]]CLEAR];exact(POINTERS value ROOT).
Qed.

Theorem gateway_reference_actual_empty_container_owned {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (constructors:gateway_objects_runtime backend python objects decimal_float)(io_projection:gateway_direct_io_projection backend io)
    context ledger held container slots arguments parameters stream_block stream_offset initial readonly original before world events value after next:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_value_stream arguments=Vptr stream_block stream_offset->parameters!_stream=Some(gateway_value_stream arguments)->
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original Int64.zero before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final,
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_wire_capture(gateway_reference_next ledger)value(gateway_container_empty_wire container)])next /\
    gateway_value_heap decimal_float(objects next)value(gateway_container_empty_wire container) /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    gateway_received_bytes io(stream_descriptor initial)events=[] /\
    (forall captured,In captured held->gateway_held_object captured<>value).
Proof.
  intros CALL FORMED STACK SCOPE STREAM STREAM_PARAMETER INPUT READONLY RUN NONNULL.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  pose proof(gateway_reference_stack_call_bound(Clight.globalenv prog)(Internal f_host_value)[]context before ledger STACK)as BOUND.
  destruct(gateway_reference_fresh_call_places _ _ _ _ _ _ BOUND)as[TEMP_FREE RESULT_FREE].
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    references ledger held runtime)as SCOPED_THREADS.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPED_THREADS readonly)as THREADS.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { intros candidate position READ;split;[eapply gateway_container_counted_readonly_live;[exact INPUT|exact READ]|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED:gateway_container_counted native stable augmented container slots stream_block stream_offset initial readonly original Int64.zero before world).
  { eapply gateway_container_counted_rebase;[exact INPUT|]. split;[split;[eapply gateway_container_counted_side;exact INPUT|exact SCOPE]|exact OWNED]. }
  destruct(actual_gateway_container_binding container)as(definition &DEFINITION &[symbol[SYMBOL FUNCTION]]&TYPE).
  destruct actual_stream_layout as[_[_[_[_[_[_[NODES_LAYOUT _]]]]]]].
  destruct(gateway_actual_container_constructor_cut backend(Clight.globalenv prog)io native stable augmented thread_errno THREADS
    container slots arguments parameters stream_block stream_offset initial readonly original Int64.zero before world events value after next
    symbol definition STREAM STREAM_PARAMETER NODES_LAYOUT SYMBOL FUNCTION TYPE AUGMENTED RUN NONNULL)
    as(called_parameters &prefix &constructing &suffix &called &called_world &result &changed &changed_world &EVENTS &QUIET &CALLED_STREAM &CALLED_DEPTH &CALLED &CONSTRUCTING &RESULT_NONNULL &REST).
  pose proof(gateway_container_counted_side _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED)as[[SIDE HELD]REGION].
  assert(CALLED_BASE:gateway_container_counted native stable base container slots stream_block stream_offset initial readonly original Int64.zero called called_world).
  { eapply gateway_container_counted_rebase;[exact CALLED|exact SIDE]. }
  destruct(gateway_reference_actual_container_allocation backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime references constructors ledger(gateway_reference_temporary(gateway_reference_depth context)_container)held container definition slots
    stream_block stream_offset initial readonly original Int64.zero called called_world constructing result changed changed_world FORMED
    (TEMP_FREE _container(gateway_reference_depth context)ltac:(lia))HELD DEFINITION CALLED_BASE
    ltac:(intros candidate position READ;exact(proj2(REGION candidate position READ)))CONSTRUCTING RESULT_NONNULL)
    as[minted[MINT[MINT_WELL[MINT_OWNED[MINT_SCOPE[MINT_COUNTED[MINT_NATIVE MINT_OUTSIDE]]]]]]].
  destruct(gateway_reference_owned_pointer python objects minted _ _ result changed changed_world
    ltac:(eapply gateway_container_counted_side;exact MINT_COUNTED)(proj1 MINT_SCOPE)MINT_OWNED)
    as(object &offset &RESULT_POINTER &POINTER);subst result.
  set(captured:=gateway_reference_wire_capture(gateway_reference_next ledger)(Vptr object offset)(gateway_container_empty_wire container)).
  set(ready:=gateway_reference_counted_context python objects decimal_float detached stable minted(held++[captured])container slots
    stream_block stream_offset initial readonly original Int64.zero).
  assert(READY:ready changed changed_world)by(exact(conj MINT_COUNTED(conj MINT_SCOPE MINT_NATIVE))).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime references
    minted(held++[captured])container slots stream_block stream_offset initial readonly original Int64.zero)as CLOSED.
  assert(VALID:forall memory current,ready memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true).
  { intros memory current[COUNTED[HOLD NATIVE]].
    destruct(gateway_reference_owned_pointer python objects minted _ _ (Vptr object offset)memory current
      ltac:(eapply gateway_container_counted_side;exact COUNTED)(proj1 HOLD)MINT_OWNED)
      as(actual &actual_offset &SAME &VALID);inversion SAME;subst;exact VALID. }
  destruct(gateway_reference_actual_container_setup backend(Clight.globalenv prog)context ledger minted container slots called_parameters object offset
    changed changed_world suffix value after next ready CLOSED VALID READY STACK MINT REST)
    as(setup_prefix &loop_events &loop_memory &loop_world &SETUP_EVENTS &SETUP_QUIET &SETUP_PREFIX &LOOP_READY &LOOP_BOUND &LOOP_PARENT &LOOP_INDEX &LOOP_RUN).
  assert(RESULT_VACANT:gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries minted)=None).
  { eapply(gateway_reference_mint_keeps_vacant ledger minted
      (gateway_reference_temporary(gateway_reference_depth context)_container)(Vptr object offset)
      (gateway_reference_result(gateway_reference_depth context)));[apply RESULT_FREE|discriminate|exact MINT]. }
  destruct(gateway_reference_actual_container_exit backend python objects decimal_float detached io stable thread_errno heap_allocation runtime references
    context minted(held++[captured])(gateway_reference_next ledger)container slots(gateway_container_setup_parameters container object offset called_parameters)
    object offset Int64.zero Int64.zero stream_block stream_offset initial readonly original loop_memory loop_world loop_events value after next
    CALL MINT_WELL MINT_OWNED RESULT_VACANT LOOP_PARENT LOOP_INDEX eq_refl LOOP_READY LOOP_RUN)
    as[final[SAME[WELL[RESULT[BINDING[FINAL_SCOPE[FINAL_CONTEXT[FINAL_NATIVE FINAL_EMPTY]]]]]]]].
  unfold captured in FINAL_SCOPE;rewrite<-SAME in FINAL_SCOPE.
  assert(HEAP:gateway_value_heap decimal_float(objects next)value(gateway_container_empty_wire container)).
  { pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ FINAL_SCOPE ltac:(apply in_or_app;right;left;reflexivity))
      as[OWNER[PRIVATE[DESTROY DESCRIPTION]]];exact DESCRIPTION. }
  exists final;split;[exact WELL|]. split;[exact RESULT|]. split;[exact BINDING|]. split;[exact FINAL_SCOPE|]. split;[exact HEAP|].
  split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split.
  - rewrite EVENTS,SETUP_EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),
    (gateway_quiet_received io(stream_descriptor initial)setup_prefix SETUP_QUIET),FINAL_EMPTY.
  rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io(gateway_container_api container)definition
    (gateway_container_constructor_values container)called called_world constructing(Vptr object offset)changed changed_world
    (stream_descriptor initial)io_projection DEFINITION CONSTRUCTING);reflexivity.
  - intros previous MEMBER EQUAL;apply(MINT_OUTSIDE previous MEMBER).
    rewrite EQUAL,SAME;constructor.
Qed.

Theorem gateway_reference_actual_empty_container {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (constructors:gateway_objects_runtime backend python objects decimal_float)(io_projection:gateway_direct_io_projection backend io)
    context ledger held container slots arguments parameters stream_block stream_offset initial readonly original before world events value after next:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_value_stream arguments=Vptr stream_block stream_offset->parameters!_stream=Some(gateway_value_stream arguments)->
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original Int64.zero before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final,
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_wire_capture(gateway_reference_next ledger)value(gateway_container_empty_wire container)])next /\
    gateway_value_heap decimal_float(objects next)value(gateway_container_empty_wire container) /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros CALL FORMED STACK SCOPE STREAM STREAM_PARAMETER INPUT READONLY RUN NONNULL.
  destruct(gateway_reference_actual_empty_container_owned backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime references constructors io_projection context ledger held container slots arguments parameters stream_block stream_offset initial readonly original
    before world events value after next CALL FORMED STACK SCOPE STREAM STREAM_PARAMETER INPUT READONLY RUN NONNULL)
    as[final[WELL[RESULT[BINDING[FINAL_SCOPE[HEAP[FINAL_CONTEXT[FINAL_NATIVE[FINAL_EMPTY FRESH]]]]]]]]].
  exists final;exact(conj WELL(conj RESULT(conj BINDING(conj FINAL_SCOPE(conj HEAP(conj FINAL_CONTEXT(conj FINAL_NATIVE FINAL_EMPTY))))))).
Qed.
