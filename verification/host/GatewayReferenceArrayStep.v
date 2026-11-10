(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same recursive child return reaches the actual append call,
   transfers its selected owner to first, and produces the next owned array snapshot. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayValueShapes GatewayValueEntry GatewayValueStack GatewayValueEnvironment
  GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayContainerLoopSource GatewayContainerArraySource
  GatewayContainerABI GatewayContainerAppendCall GatewayContainerAppendReceipt GatewayReferenceArrayContextRun GatewayReferenceSnapshotInputs
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceMoves
  GatewayReferenceNormalForm GatewayReferenceChildOwnership GatewayReferenceLoopLedger GatewayReferenceStackBound
  GatewayReferenceGraphCapture GatewayReferenceContainerScope GatewayReferenceContainerContext GatewayReferenceValueProperties
  GatewayGraphSnapshots GatewayReadonly GatewayPathEvents GatewayReturnRuntime GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_array_step {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
    (excluded:Values.val->Prop)context older parent_ledger child_ledger held parent_ticket parent parent_offset pointers values parent_initial
    child_ticket child child_offset child_value child_initial slots parameters stream_block stream_offset initial readonly original size
    before world events value after next append_symbol append_definition release_symbol release_definition:
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed child_ledger->
  gateway_reference_loop_entries context older parent_ledger parent_ticket(Vptr parent parent_offset)->
  gateway_reference_result_entries(plug_cont(gateway_container_first_cont slots parameters)context)parent_ledger child_ledger
    (child_ticket)(Vptr child child_offset)->
  gateway_reference_graphs_only held->gateway_reference_snapshots_avoid held(Vptr parent parent_offset)->
  gateway_object_values parent_initial(Vptr parent parent_offset)=Some(gateway_list_object pointers)->
  gateway_array_heap decimal_float parent_initial pointers values->
  (forall pointer,In pointer pointers->~gateway_object_reachable parent_initial pointer(Vptr parent parent_offset))->
  ~gateway_object_reachable child_initial(Vptr child child_offset)(Vptr parent parent_offset)->
  (forall pointer,excluded pointer->~gateway_object_reachable parent_initial(Vptr parent parent_offset)pointer /\
    ~gateway_object_reachable child_initial(Vptr child child_offset)pointer)->
  parameters!_container=Some(Vptr parent parent_offset)->
  gateway_reference_counted_context python objects decimal_float detached stable child_ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))parent_initial;
      gateway_reference_graph_capture(child_ticket)(Vptr child child_offset)child_value child_initial])
    gateway_container_array slots stream_block stream_offset initial readonly original size before world->
  gateway_object_api_definition gateway_api_list_append=Some append_definition->
  Genv.find_symbol ge _PyList_Append=Some append_symbol->Genv.find_funct_ptr ge append_symbol=Some append_definition->
  type_of_fundef append_definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default->
  Genv.find_symbol ge _Py_DecRef=Some release_symbol->Genv.find_funct_ptr ge release_symbol=Some release_definition->
  type_of_fundef release_definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr child child_offset)(gateway_container_first_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists adopted called_parameters prefix appending suffix append_before append_world append_after append_next,
    events=prefix++appending++suffix /\Forall gateway_quiet_event prefix /\
    gateway_reference_ledger_well_formed adopted /\
    gateway_reference_entries adopted=gateway_reference_entry(child_ticket)
      (gateway_reference_temporary(gateway_reference_depth context)_first)(Vptr child child_offset)::gateway_reference_entries parent_ledger /\
    gateway_reference_next adopted=gateway_reference_next child_ledger /\
    gateway_reference_apply(gateway_reference_move
      (gateway_reference_result(gateway_reference_depth(plug_cont(gateway_container_first_cont slots parameters)context)))
      (gateway_reference_temporary(gateway_reference_depth context)_first))(gateway_reference_valid child_ledger)=gateway_reference_valid adopted /\
    called_parameters!_container=Some(Vptr parent parent_offset) /\called_parameters!_first=Some(Vptr child child_offset) /\
    called_parameters!_stream=parameters!_stream /\called_parameters!_depth=parameters!_depth /\
    called_parameters!_index__1=parameters!_index__1 /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vptr child child_offset)(gateway_container_first_cont slots parameters)before)world)prefix
      (gateway_live(Callstate append_definition[Vptr parent parent_offset;Vptr child child_offset]
        (gateway_container_append_cont slots called_parameters)append_before)append_world) /\
    gateway_steps backend ge
      (gateway_live(Callstate append_definition[Vptr parent parent_offset;Vptr child child_offset]Kstop append_before)append_world)appending
      (gateway_live(Returnstate(Vint Int.zero)Kstop append_after)append_next) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_container_append_cont slots called_parameters)append_after)append_next)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_reference_counted_context python objects decimal_float detached stable adopted
      (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
        (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values(values++[child_value])))(objects append_next)])
      gateway_container_array slots stream_block stream_offset initial readonly original size append_after append_next /\
    gateway_object_values(objects append_next)(Vptr parent parent_offset)=Some(gateway_list_object(pointers++[Vptr child child_offset])) /\
    gateway_array_heap decimal_float(objects append_next)(pointers++[Vptr child child_offset])(values++[child_value]) /\
    (forall pointer,In pointer(pointers++[Vptr child child_offset])->
      ~gateway_object_reachable(objects append_next)pointer(Vptr parent parent_offset)) /\
    (forall pointer,excluded pointer->~gateway_object_reachable(objects append_next)(Vptr parent parent_offset)pointer).
Proof.
  intros STACK FORMED LOOP_ENTRIES CHILD_ENTRIES GRAPHS OLD_OUTSIDE LOOKUP ARRAY ACYCLIC CHILD_OUTSIDE EXCLUDED PARENT INPUT
    DEFINITION SYMBOL FUNCTION TYPE RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE RUN NONNULL.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(parent_capture:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))parent_initial).
  set(child_capture:=gateway_reference_graph_capture(child_ticket)(Vptr child child_offset)child_value child_initial).
  set(all_held:=held++[parent_capture;child_capture]).
  set(property:=gateway_reference_counted_context python objects decimal_float detached stable child_ledger all_held
    gateway_container_array slots stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads child_ledger all_held gateway_container_array slots stream_block stream_offset initial readonly original size)as CLOSED.
  assert(PARENT_OWNED:gateway_reference_owns child_ledger
    (gateway_reference_temporary(gateway_reference_depth context)_container)parent_ticket(Vptr parent parent_offset)).
  { unfold gateway_reference_owns;rewrite CHILD_ENTRIES;right;rewrite LOOP_ENTRIES;left;reflexivity. }
  assert(SNAPSHOT_INPUTS:forall memory current,property memory current->
    gateway_objects_ready(python current)(objects current)memory /\
    gateway_rooted(python current)(objects current)(Vptr parent parent_offset) /\
    gateway_rooted(python current)(objects current)(Vptr child child_offset) /\
    gateway_object_values(objects current)(Vptr parent parent_offset)=Some(gateway_list_object pointers)).
  { intros memory current[COUNTED[SCOPE NATIVE]].
    destruct(gateway_reference_array_snapshot_inputs python objects decimal_float child_ledger held current
      _ parent_ticket(Vptr parent parent_offset)pointers values parent_initial(child_ticket)
      (Vptr child child_offset)child_value child_initial SCOPE PARENT_OWNED GRAPHS OLD_OUTSIDE LOOKUP ARRAY ACYCLIC CHILD_OUTSIDE)
      as[SELECTED[CHILD_ROOT[PRIVATE[DESTROY[VALUES REST]]]]].
    split;[eapply gateway_container_counted_side;exact COUNTED|]. split;
      [eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact PARENT_OWNED]|]. split;assumption. }
  assert(POINTER:forall memory current,property memory current->Mem.weak_valid_pointer memory child(Ptrofs.unsigned child_offset)=true).
  { intros memory current GOOD;destruct(SNAPSHOT_INPUTS memory current GOOD)as[READY[PARENT_ROOT[CHILD_ROOT REST]]].
    destruct READY as[[_[_[_[_ POINTERS]]]]CLEAR].
    destruct(POINTERS(Vptr child child_offset)CHILD_ROOT)as[actual[offset[SAME VALID]]];inversion SAME;subst;exact VALID. }
  destruct(gateway_actual_array_append_receipt backend ge python objects abi property slots parameters parent parent_offset child child_offset pointers
    before world events value after next append_symbol append_definition release_symbol release_definition DEFINITION CLOSED PARENT SNAPSHOT_INPUTS POINTER
    ltac:(intros memory current[COUNTED REST];exact(proj2(proj1 COUNTED)))SYMBOL FUNCTION TYPE RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE INPUT RUN NONNULL)
    as(called_parameters &prefix &appending &suffix &append_before &append_world &append_after &append_next &EVENTS &QUIET &CALLED_PARENT &CALLED_CHILD &
      CALLED_STREAM &CALLED_DEPTH &CALLED_INDEX &CALLED &TO_APPEND &APPENDING &REST).
  pose proof CALLED as[COUNTED[SCOPE NATIVE]].
  destruct(gateway_reference_adopt_child python objects decimal_float
    (plug_cont(gateway_container_first_cont slots parameters)context)parent_ledger child_ledger(child_ticket)
    (Vptr child child_offset)all_held append_world(gateway_reference_temporary(gateway_reference_depth context)_first)FORMED CHILD_ENTRIES
    ltac:(discriminate)
    ltac:(eapply gateway_reference_loop_free;[exact STACK|exact LOOP_ENTRIES|discriminate])SCOPE)
    as[adopted[MOVE[WELL[ADOPTED_ENTRIES[NEXT[CHILD_OWNED ADOPTED_SCOPE]]]]]].
  assert(ADOPTED_PARENT:gateway_reference_owns adopted
    (gateway_reference_temporary(gateway_reference_depth context)_container)parent_ticket(Vptr parent parent_offset)).
  { unfold gateway_reference_owns;rewrite ADOPTED_ENTRIES;right;rewrite LOOP_ENTRIES;left;reflexivity. }
  set(adopted_property:=gateway_reference_counted_context python objects decimal_float detached stable adopted all_held
    gateway_container_array slots stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads adopted all_held gateway_container_array slots stream_block stream_offset initial readonly original size)as ADOPTED_CLOSED.
  destruct(gateway_reference_actual_array_context_run backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads containers excluded slots stream_block stream_offset initial readonly original size adopted(held++[child_capture])
    (gateway_reference_temporary(gateway_reference_depth context)_container)parent_ticket(Vptr parent parent_offset)pointers values
    (Vptr child child_offset)child_value append_definition(gateway_value_environment slots)adopted_property append_before append_world appending append_after append_next
    DEFINITION ADOPTED_CLOSED
    ltac:(intros memory current[CURRENT_COUNTED[CURRENT_SCOPE CURRENT_NATIVE]];
      destruct(gateway_reference_array_snapshot_inputs python objects decimal_float adopted held current
        _ parent_ticket(Vptr parent parent_offset)pointers values parent_initial(child_ticket)
        (Vptr child child_offset)child_value child_initial CURRENT_SCOPE ADOPTED_PARENT GRAPHS OLD_OUTSIDE LOOKUP ARRAY ACYCLIC CHILD_OUTSIDE)
      as(SELECTED &CHILD_ROOT &PRIVATE &DESTROY &VALUES &ARRAY_VALUE &CHILD_PRIVATE &CHILD_DESTROY &CHILD_VALUE &NO_CYCLE &OUTSIDE);
      assert(NO_PATH:forall pointer,excluded pointer->~gateway_object_reachable(objects current)(Vptr parent parent_offset)pointer /\
        ~gateway_object_reachable(objects current)(Vptr child child_offset)pointer)by
        (intros pointer FORBIDDEN;destruct(EXCLUDED pointer FORBIDDEN)as[PARENT_OUTSIDE CHILD_OUTSIDE_EXCLUDED];split;
          [eapply gateway_reference_graph_exclusion;[exact CURRENT_SCOPE|unfold all_held;apply in_or_app;right;left;reflexivity|exact PARENT_OUTSIDE]|
           eapply gateway_reference_graph_exclusion;[exact CURRENT_SCOPE|unfold all_held;apply in_or_app;right;right;left;reflexivity|exact CHILD_OUTSIDE_EXCLUDED]]);
      exact(conj SELECTED(conj ADOPTED_PARENT(conj CHILD_ROOT(conj PRIVATE(conj DESTROY(conj VALUES(conj ARRAY_VALUE
        (conj CHILD_PRIVATE(conj CHILD_DESTROY(conj CHILD_VALUE(conj NO_CYCLE(conj OUTSIDE(conj CURRENT_COUNTED(conj CURRENT_NATIVE NO_PATH)))))))))))))))
    (conj COUNTED(conj ADOPTED_SCOPE NATIVE))
    ltac:(split;[eapply gateway_container_counted_side;exact COUNTED|eapply GatewayValueEnvironment.gateway_value_active_environment;exact(proj1(proj1 COUNTED))])APPENDING)
    as[UPDATED_SCOPE[UPDATED_LOOKUP[UPDATED_ACYCLIC[UPDATED_ENV[UPDATED_COUNTED[UPDATED_NATIVE[UPDATED_EXCLUDED ORIGIN]]]]]]].
  pose proof(gateway_reference_upgrade_wire_capture python objects decimal_float adopted(held++[child_capture])append_next parent_ticket
    (Vptr parent parent_offset)(LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values(values++[child_value])))UPDATED_SCOPE)as UPGRADED.
  assert(FINAL_SCOPE:gateway_reference_scope python objects decimal_float adopted
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values(values++[child_value])))(objects append_next)])append_next).
  { eapply gateway_reference_scope_sublist;[exact UPGRADED|]. intros captured MEMBER;apply in_app_or in MEMBER;apply in_or_app;
      destruct MEMBER as[OLD|[SAME|EMPTY]];
      [left;apply in_or_app;left;exact OLD|right;left;exact SAME|contradiction]. }
  assert(UPDATED_VALUE:gateway_value_heap decimal_float(objects append_next)(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values(values++[child_value])))).
  { pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ FINAL_SCOPE
      ltac:(apply in_or_app;right;left;reflexivity))as[OWNER[PRIVATE[DESTROY[VALUE SNAPSHOT]]]];exact VALUE. }
  exists adopted,called_parameters,prefix,appending,suffix,append_before,append_world,append_after,append_next.
  split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact WELL|]. split;[exact ADOPTED_ENTRIES|]. split;[exact NEXT|]. split;[exact MOVE|].
  split;[exact CALLED_PARENT|]. split;[exact CALLED_CHILD|]. split;[exact CALLED_STREAM|]. split;[exact CALLED_DEPTH|]. split;[exact CALLED_INDEX|].
  split;[exact TO_APPEND|]. split;[exact APPENDING|]. split;[exact REST|]. split;[exact(conj UPDATED_COUNTED(conj FINAL_SCOPE UPDATED_NATIVE))|].
  split;[exact UPDATED_LOOKUP|]. split;[eapply gateway_array_heap_from_value;eassumption|]. split;[exact UPDATED_ACYCLIC|exact UPDATED_EXCLUDED].
Qed.
