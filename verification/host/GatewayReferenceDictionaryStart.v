(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual checked count return, guarded allocation and setup
   establish the owned empty-object loop frontier consumed by the recursive fold. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayValue GatewayValueOwnership GatewayValueEntry GatewayValueContext GatewayValueStack GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayContainerAllocation
  GatewayContainerCalls GatewayContainerConstructorReceipt GatewayContainerSetup GatewayContainerSetupReceipt GatewayContainerLoopSource GatewayDictionaryEmptyShape
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceStackBound GatewayReferenceActivation GatewayReferenceNormalForm
  GatewayReferenceContainerAllocation GatewayReferenceContainerScope GatewayReferenceContainerContext GatewayReferenceEmptyContainer
  GatewayReferenceGraphCapture GatewayReferenceValueProperties GatewayReferenceAncestors GatewayReferenceSnapshotInputs GatewayNativeRegions GatewayRegionThreads
  GatewayThreadInvariant GatewayReadonly GatewayPathEvents GatewayObjectEvents GatewayObjectRuns GatewayStreamLayout GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_dictionary_start {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (constructors:gateway_objects_runtime backend python objects decimal_float)(projection:gateway_direct_io_projection backend io)
    context ledger held slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_scope python objects decimal_float ledger held world->gateway_reference_graphs_only held->
  gateway_value_stream arguments=Vptr stream_block stream_offset->parameters!_stream=Some(gateway_value_stream arguments)->
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)gateway_container_object slots stream_block stream_offset initial readonly original size before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists minted parent offset parent_snapshot loop_parameters prefix suffix loop_memory loop_world,
    events=prefix++suffix /\(forall descriptor,gateway_received_bytes io descriptor prefix=[]) /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_temporary(gateway_reference_depth context)_container)(Vptr parent offset))
      (gateway_reference_valid ledger)=gateway_reference_valid minted /\gateway_reference_ledger_well_formed minted /\
    gateway_reference_entries minted=gateway_reference_entry(gateway_reference_next ledger)
      (gateway_reference_temporary(gateway_reference_depth context)_container)(Vptr parent offset)::gateway_reference_entries ledger /\
    gateway_object_values parent_snapshot(Vptr parent offset)=Some(gateway_dict_object[]) /\
    gateway_reference_snapshots_avoid held(Vptr parent offset) /\
    (forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable parent_snapshot(Vptr parent offset)pointer) /\
    loop_parameters!_container=Some(Vptr parent offset) /\loop_parameters!_stream=Some(gateway_value_stream arguments) /\
    loop_parameters!_depth=parameters!_depth /\loop_parameters!_index__1=Some(Vlong Int64.zero) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)before)world)prefix
      (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)loop_parameters loop_memory)loop_world) /\
    gateway_reference_counted_context python objects decimal_float detached stable minted
      (held++[gateway_reference_graph_capture(gateway_reference_next ledger)(Vptr parent offset)
        (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields[]))parent_snapshot])
      gateway_container_object slots stream_block stream_offset initial readonly original size loop_memory loop_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)loop_parameters loop_memory)loop_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros FORMED STACK SCOPE GRAPHS STREAM STREAM_PARAMETER INPUT READONLY RUN NONNULL.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  pose proof(gateway_reference_stack_call_bound(Clight.globalenv prog)(Internal f_host_value)[]context before ledger STACK)as BOUND.
  destruct(gateway_reference_fresh_call_places _ _ _ _ _ _ BOUND)as[TEMP_FREE RESULT_FREE].
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    reference_threads ledger held runtime)as SCOPED_THREADS.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPED_THREADS readonly)as THREADS.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { intros candidate position READ;split;[eapply gateway_container_counted_readonly_live;[exact INPUT|exact READ]|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED:gateway_container_counted native stable augmented gateway_container_object slots stream_block stream_offset initial readonly original size before world).
  { eapply gateway_container_counted_rebase;[exact INPUT|]. split;[split;[eapply gateway_container_counted_side;exact INPUT|exact SCOPE]|exact OWNED]. }
  destruct(actual_gateway_container_binding gateway_container_object)as(definition &DEFINITION &[symbol[SYMBOL FUNCTION]]&TYPE).
  destruct actual_stream_layout as[_[_[_[_[_[_[NODES_LAYOUT _]]]]]]].
  destruct(gateway_actual_container_constructor_receipt backend(Clight.globalenv prog)io native stable augmented thread_errno THREADS
    gateway_container_object slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next
    symbol definition STREAM STREAM_PARAMETER NODES_LAYOUT SYMBOL FUNCTION TYPE AUGMENTED RUN NONNULL)
    as(called_parameters &source_prefix &constructing &rest &called &called_world &result &changed &changed_world &EVENTS &QUIET &CALLED_STREAM &CALLED_DEPTH &CALLED &TO_CONSTRUCTOR &CONSTRUCTING &RESULT_NONNULL &REST).
  pose proof(gateway_container_counted_side _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED)as[[SIDE HELD]REGION].
  assert(CALLED_BASE:gateway_container_counted native stable base gateway_container_object slots stream_block stream_offset initial readonly original size called called_world).
  { eapply gateway_container_counted_rebase;[exact CALLED|exact SIDE]. }
  destruct(gateway_reference_actual_container_allocation backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads constructors ledger(gateway_reference_temporary(gateway_reference_depth context)_container)held gateway_container_object definition slots
    stream_block stream_offset initial readonly original size called called_world constructing result changed changed_world FORMED
    (TEMP_FREE _container(gateway_reference_depth context)ltac:(lia))HELD DEFINITION CALLED_BASE
    ltac:(intros candidate position READ;exact(proj2(REGION candidate position READ)))CONSTRUCTING RESULT_NONNULL)
    as[minted[MINT[MINT_WELL[MINT_OWNED[MINT_SCOPE[MINT_COUNTED[MINT_NATIVE MINT_OUTSIDE]]]]]]].
  destruct(gateway_reference_owned_pointer python objects minted _ _ result changed changed_world
    ltac:(eapply gateway_container_counted_side;exact MINT_COUNTED)(proj1 MINT_SCOPE)MINT_OWNED)
    as(parent &offset &POINTER &VALID);subst result.
  pose proof(gateway_reference_upgrade_wire_capture python objects decimal_float minted held changed_world(gateway_reference_next ledger)
    (Vptr parent offset)(gateway_container_empty_wire gateway_container_object)MINT_SCOPE)as GRAPH_SCOPE.
  set(captured:=gateway_reference_graph_capture(gateway_reference_next ledger)(Vptr parent offset)
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields[]))(objects changed_world)).
  assert(HEAP:gateway_value_heap decimal_float(objects changed_world)(Vptr parent offset)
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields[]))).
  { pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ GRAPH_SCOPE
      ltac:(apply in_or_app;right;left;reflexivity))as[PLACE[PRIVATE[DESTROY[VALUE SNAPSHOT]]]];exact VALUE. }
  pose proof(gateway_empty_dictionary_lookup _ _ _ HEAP)as LOOKUP.
  assert(OLD_SCOPE:gateway_reference_scope python objects decimal_float minted held changed_world).
  { eapply gateway_reference_scope_sublist;[exact GRAPH_SCOPE|intros previous MEMBER;apply in_or_app;left;exact MEMBER]. }
  assert(SNAPSHOTS:gateway_reference_snapshots_avoid held(Vptr parent offset)).
  { eapply gateway_reference_fresh_snapshot_exclusion;[exact OLD_SCOPE|exact GRAPHS|exact MINT_OUTSIDE]. }
  assert(EXCLUDED:forall pointer,gateway_reference_mutable_target held pointer->
    ~gateway_object_reachable(objects changed_world)(Vptr parent offset)pointer).
  { intros pointer[captured_before[wire[old_heap[old_value[MEMBER[VIEW[OLD_VALUE[MUTABLE SAME]]]]]]]]REACHED.
    pose proof(gateway_leaf_reachable _ _ _ _ LOOKUP eq_refl REACHED)as EQUAL.
    apply(MINT_OUTSIDE captured_before MEMBER).
    assert(ROOT:gateway_held_object captured_before=Vptr parent offset)by congruence;rewrite ROOT;constructor. }
  set(ready:=gateway_reference_counted_context python objects decimal_float detached stable minted(held++[captured])gateway_container_object slots
    stream_block stream_offset initial readonly original size).
  assert(READY:ready changed changed_world)by(exact(conj MINT_COUNTED(conj GRAPH_SCOPE MINT_NATIVE))).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    minted(held++[captured])gateway_container_object slots stream_block stream_offset initial readonly original size)as CLOSED.
  assert(LIVE:forall memory current,ready memory current->Mem.weak_valid_pointer memory parent(Ptrofs.unsigned offset)=true).
  { intros memory current[COUNTED[HOLD NATIVE]].
    destruct(gateway_reference_owned_pointer python objects minted _ _ (Vptr parent offset)memory current
      ltac:(eapply gateway_container_counted_side;exact COUNTED)(proj1 HOLD)MINT_OWNED)
      as(actual &actual_offset &SAME &VALID_POINTER);inversion SAME;subst;exact VALID_POINTER. }
  destruct(gateway_reference_actual_container_setup backend(Clight.globalenv prog)context ledger minted gateway_container_object slots called_parameters parent offset
    changed changed_world rest value after next ready CLOSED LIVE READY STACK MINT REST)
    as(setup_prefix &suffix &loop_memory &loop_world &SETUP_EVENTS &SETUP_QUIET &SETUP_PREFIX &LOOP_READY &LOOP_BOUND &LOOP_PARENT &LOOP_INDEX &LOOP_RUN).
  exists minted,parent,offset,(objects changed_world),(gateway_container_setup_parameters gateway_container_object parent offset called_parameters),
    (source_prefix++constructing++setup_prefix),suffix,loop_memory,loop_world.
  split;[rewrite EVENTS,SETUP_EVENTS;repeat rewrite app_assoc;reflexivity|]. split.
  - intros descriptor;rewrite !gateway_received_append,(gateway_quiet_received io descriptor source_prefix QUIET),
      (gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_dict_new definition[]called called_world
        constructing(Vptr parent offset)changed changed_world descriptor projection DEFINITION CONSTRUCTING),
      (gateway_quiet_received io descriptor setup_prefix SETUP_QUIET);reflexivity.
  - split;[exact MINT|]. split;[exact MINT_WELL|]. split;
      [exact(proj1(gateway_reference_mint_entries ledger minted(gateway_reference_temporary(gateway_reference_depth context)_container)(Vptr parent offset)MINT))|].
    split;[exact LOOKUP|]. split;[exact SNAPSHOTS|]. split;[exact EXCLUDED|]. split;[exact LOOP_PARENT|]. split.
    + unfold gateway_container_setup_parameters,set_opttemp,gateway_container_constructor_destination;repeat rewrite PTree.gso by discriminate;exact CALLED_STREAM.
    + split;[unfold gateway_container_setup_parameters,set_opttemp,gateway_container_constructor_destination;repeat rewrite PTree.gso by discriminate;exact CALLED_DEPTH|]. split;[exact LOOP_INDEX|]. split.
      * eapply gateway_steps_append;[exact TO_CONSTRUCTOR|]. eapply gateway_steps_append;[|exact SETUP_PREFIX].
        exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _ (gateway_container_constructor_cont gateway_container_object slots called_parameters)
          ltac:(cbn;exact I)CONSTRUCTING).
      * split;assumption.
Qed.
