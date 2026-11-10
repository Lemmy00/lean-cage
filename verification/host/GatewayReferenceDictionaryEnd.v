(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual exhausted dictionary loop returns its owned completed
   graph through real local cleanup, retaining earlier source owners and observations. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Values Memory Integers Ctypes Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayContainerLength GatewayContainerLoopSource
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferencePlaces GatewayReferenceThreads GatewayReferenceStackBound GatewayReferenceLoopLedger
  GatewayReferenceNormalForm GatewayReferenceOwnedContainerExit GatewayReferenceDecoded GatewayReferenceGraphCapture GatewayReferenceContainerScope
  GatewayReferenceContainerContext GatewayReferenceValueProperties GatewayReferenceAncestors GatewayArrayBounds GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_dictionary_end {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    context older ledger held parent_ticket parent parent_offset values parent_initial slots parameters index size
    stream_block stream_offset initial readonly original before world events value after next:
  is_call_cont context->gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_loop_entries context older ledger parent_ticket(Vptr parent parent_offset)->
  (gateway_reference_next older<=parent_ticket)%nat->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries ledger)=None->
  (forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable parent_initial(Vptr parent parent_offset)pointer)->
  parameters!GatewaySource._container=Some(Vptr parent parent_offset)->parameters!GatewaySource._index__1=Some(Vlong index)->
  Int64.ltu index size=false->
  gateway_reference_counted_context python objects decimal_float detached stable ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))parent_initial])
    gateway_container_object slots stream_block stream_offset initial readonly original size before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final,value=Vptr parent parent_offset /\
    gateway_reference_decoded python objects decimal_float(Clight.globalenv prog)context older held
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))parent_ticket value final after next /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros CALL STACK FORMED ENTRIES FRESH VACANT EXCLUDED PARENT INDEX EXHAUSTED INPUT RUN.
  assert(PARENT_OWNED:gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_container)
    parent_ticket(Vptr parent parent_offset)).
  { unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity. }
  destruct(gateway_reference_actual_container_exit_owned backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads context older ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))parent_initial])parent_ticket gateway_container_object slots parameters
    parent parent_offset index size stream_block stream_offset initial readonly original before world events value after next
    CALL FORMED STACK ENTRIES PARENT_OWNED VACANT PARENT INDEX EXHAUSTED INPUT RUN)
    as(final &SAME &WELL &OWNER &BINDING &SCOPE &FINAL_CONTEXT &FINAL_NATIVE &EMPTY &RESULT_ENTRIES &BOUND).
  subst value.
  set(captured:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))parent_initial).
  assert(MEMBER:In captured(held++[captured]))by(apply in_or_app;right;left;reflexivity).
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[PLACE[PRIVATE[DESTROY[VALUE SNAPSHOT]]]].
  assert(REFRESHED:gateway_reference_scope python objects decimal_float final
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))(objects next)])next).
  { exact(gateway_reference_graph_result python objects decimal_float final held captured next _ SCOPE VALUE). }
  assert(AVOIDS:gateway_reference_avoids_old_mutable held(objects next)(Vptr parent parent_offset)).
  { apply(proj2(gateway_reference_avoids_targets _ _ _));intros pointer FORBIDDEN.
    eapply gateway_reference_graph_exclusion;[exact SCOPE|exact MEMBER|apply EXCLUDED;exact FORBIDDEN]. }
  exists final;split;[reflexivity|]. split.
  - constructor;assumption.
  - split;[exact FINAL_CONTEXT|]. split;assumption.
Qed.
