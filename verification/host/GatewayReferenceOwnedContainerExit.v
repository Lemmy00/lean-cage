(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Exhausting the real source loop returns its selected owned graph
   while freeing only the actual local word cells and retaining the same stream. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps LocalAccess CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayObjectDiscipline GatewayReferences
  GatewayValue GatewayValueEntry GatewayValueEnvironment GatewayValueContext GatewayValueStack GatewayValueReturnContext
  GatewayContainerLength GatewayContainerGuards GatewayContainerLoopSource GatewayContainerExit GatewayContainerMemory
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceFrames GatewayReferenceSourceReturn GatewayReferenceOwnedReturn GatewayReferenceNormalForm GatewayReferenceStackBound GatewayReferenceThreads
  GatewayReferenceContainerContext GatewayReferenceContainerScope GatewayReferenceActivation GatewayNativeRegions
  GatewayReturnRuntime GatewayReturnMemory GatewaySourceSegments GatewayReturnIdentity GatewayPathEvents
  GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_container_exit_owned {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    context initial_ledger ledger held ticket container slots parameters object offset index size
    stream_block stream_offset initial readonly original before world events value after next:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->
  gateway_reference_stack_bound context initial_ledger->
  gateway_reference_entries ledger=gateway_reference_entry ticket
    (gateway_reference_temporary(gateway_reference_depth context)_container)(Vptr object offset)::
    gateway_reference_entries initial_ledger->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_container)ticket(Vptr object offset)->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries ledger)=None->
  parameters!_container=Some(Vptr object offset)->parameters!_index__1=Some(Vlong index)->Int64.ltu index size=false->
  gateway_reference_counted_context python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final,
    value=Vptr object offset /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))ticket value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final held next /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    gateway_received_bytes io(stream_descriptor initial)events=[] /\
    gateway_reference_result_entries context initial_ledger final ticket value /\
    gateway_reference_source_bound(Clight.globalenv prog)(Returnstate value context after)final.
Proof.
  intros CALL FORMED OLDER HEAD OWNED VACANT PARENT INDEX EXHAUSTED INPUT RUN.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(property:=gateway_reference_counted_context python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime references ledger held container slots stream_block stream_offset initial readonly original size)as CLOSED.
  pose proof(gateway_container_loop_exit_segment backend(Clight.globalenv prog)property slots parameters index size before CLOSED INDEX EXHAUSTED
    ltac:(intros memory current[COUNTED REST];exact(proj2 COUNTED)))as SEGMENT.
  destruct(gateway_source_segment_cut backend(Clight.globalenv prog)_ _ _ _ SEGMENT before world events value after next INPUT RUN)
    as(prefix &suffix &return_memory &return_world &EVENTS &QUIET &PREFIX &[COUNTED[SCOPE NATIVE]]&REST).
  set(return_parameters:=gateway_container_exit_parameters size parameters).
  assert(CONTAINER:return_parameters!_container=Some(Vptr object offset)).
  { unfold return_parameters,gateway_container_exit_parameters;rewrite PTree.gso by discriminate;exact PARENT. }
  assert(ACTIVE:gateway_value_active native stable base slots stream_block stream_offset initial readonly original return_memory return_world)
    by(exact(proj1(proj1 COUNTED))).
  pose proof(gateway_value_active_environment native stable base slots stream_block stream_offset initial readonly original return_memory return_world ACTIVE)
    as ENVIRONMENT.
  destruct(gateway_reference_context_return_entries backend(Clight.globalenv prog)context python objects decimal_float io native stable base thread_errno
    heap_allocation runtime references f_host_value _container(gateway_value_environment slots)return_parameters gateway_container_return_expression
    (Kseq gateway_value_after_container Kstop)(Vptr object offset)return_memory return_world suffix value after next initial_ledger ledger ticket held
    CALL eq_refl eq_refl
    ltac:(intros;eapply old_expression_value,value_temp;exact CONTAINER)
    ltac:(intros memory converted CAST;eapply(gateway_pointer_cast_identity memory(tptr(Tstruct __object noattr))
      (tptr(Tstruct __object noattr))(Vptr object offset)converted);[eexists;reflexivity|eexists;reflexivity|exact CAST])
    FORMED OWNED VACANT OLDER ltac:(exact HEAD)SCOPE ENVIRONMENT REST)
    as(final &SAME &EXECUTION &WELL &RESULT &BINDING &HELD &SIDE &QUIET_RETURN &ENTRIES &FINAL_BOUND).
  set(protected:=gateway_value_input_region stream_block stream_offset readonly).
  assert(REGION:gateway_native_region_owned native protected return_memory return_world).
  { eapply gateway_value_return_native_region;[exact(proj1 ACTIVE)|exact NATIVE]. }
  assert(AVOIDS:GatewayScopedMemory.gateway_environment_avoids protected(gateway_value_environment slots)).
  { eapply gateway_value_environment_avoids_inputs;exact ACTIVE. }
  pose proof(gateway_actual_return_memory backend(Clight.globalenv prog)io native stable base thread_errno runtime None f_host_value
    (Some gateway_container_return_expression)(Kseq gateway_value_after_container Kstop)(gateway_value_environment slots)return_parameters
    protected return_memory return_memory return_world suffix value after next eq_refl AVOIDS
    (conj ENVIRONMENT(conj REGION(Mem.unchanged_on_refl _ _)))REST)as[AFTER_SIDE[AFTER_OWNED FRAME]].
  assert(FINAL_CONTEXT:gateway_value_context native stable base stream_block stream_offset initial readonly original after next).
  { eapply gateway_value_context_return_frame;[exact runtime|exact(proj1 ACTIVE)|exact AFTER_SIDE|exact AFTER_OWNED|exact FRAME]. }
  exists final;split;[exact SAME|]. split;[exact WELL|]. split;[rewrite SAME;exact RESULT|].
  split;[rewrite SAME in BINDING|-*;exact BINDING|]. split;[exact HELD|]. split;[exact FINAL_CONTEXT|]. split.
  - intros candidate position READ;exact(proj2(AFTER_OWNED candidate position(or_intror READ))).
  - split.
    + rewrite EVENTS,gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),
      (gateway_quiet_received io(stream_descriptor initial)suffix QUIET_RETURN);reflexivity.
    + split;[rewrite SAME;exact ENTRIES|exact FINAL_BOUND].
Qed.
