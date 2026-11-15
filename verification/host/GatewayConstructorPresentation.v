(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original constructor supplies the actual nonnull
   callback-helper return. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectDiscipline GatewayObjectThreads GatewayThreadRuntime GatewayStreamInterface GatewayContexts GatewayReferenceLedger
  GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceStackBound GatewayReferenceActivation GatewayReferenceNormalForm
  GatewayReferenceHeld GatewayReferenceThreads GatewayPresentationRuntime GatewayPresentationTrace GatewayPresentationCredits GatewayPresentationContext
  GatewayOutcomePresentation GatewayOutcomeFields GatewayOutcomeMetadata GatewayOutcomeOutputSource GatewayOutcomePathSource.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_constructor_presentation {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples decimal_float detached io stable thread_errno heap_allocation
    (thread:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_reference_runtime backend python objects)
    (metadata:gateway_presentation_reference_runtime backend python objects tuples)
    (presentation:gateway_presentation_runtime backend python objects tuples(fun current object=>gateway_native_private(python current)object))
    context older held reserved captured protected source environment parameters output child child_offset callable callable_offset
    original copy copy_ticket fields wires metadata_field observation wire before world events value after next:
  gateway_presentation_bindings ge ->is_call_cont context ->
  gateway_reference_stack_bound(plug_cont(gateway_outcome_path_cont environment parameters)context)older ->
  gateway_reference_ledger_well_formed older ->In captured held ->In(Vptr callable callable_offset)reserved ->
  gateway_reference_owns older(gateway_reference_temporary(gateway_reference_depth context)_copy)copy_ticket copy ->
  gateway_object_values(objects world)original=Some(gateway_dict_object fields) ->
  gateway_private_tree(objects world)original ->gateway_destructible(objects world)original ->
  gateway_dictionary_heap decimal_float(objects world)fields wires ->
  gateway_outcome_fields_view python objects decimal_float copy fields wires world ->
  gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field observation wire world ->
  (forall position,(0<=position<8)%Z->protected output position) ->
  gateway_presentation_context python objects decimal_float older held reserved captured protected source output Ptrofs.zero
    (Vptr child child_offset)before world ->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_call_objects)
    [Vptr callable callable_offset;Vptr output Ptrofs.zero;Vint Int.one](gateway_outcome_path_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists reading suffix returned object offset memory current final,
    events=reading++suffix /\returned=Vptr object offset /\
    gateway_steps backend ge(gateway_live(Callstate(Internal f_host_call_objects)
      [Vptr callable callable_offset;Vptr output Ptrofs.zero;Vint Int.one]Kstop before)world)reading
      (gateway_live(Returnstate returned Kstop memory)current) /\
    gateway_steps backend ge(gateway_live(Returnstate returned(gateway_outcome_path_cont environment parameters)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=gateway_reference_entry(S(S(gateway_reference_next older)))
      (gateway_reference_result(S(gateway_reference_depth context)))returned::gateway_reference_entries older /\
    gateway_reference_next final=S(S(S(gateway_reference_next older))) /\
    gateway_presentation_context python objects decimal_float final held reserved captured protected source output Ptrofs.zero
      (Vptr child child_offset)memory current /\
    gateway_reference_owns final(gateway_reference_temporary(gateway_reference_depth context)_copy)copy_ticket copy /\
    gateway_outcome_fields_view python objects decimal_float copy fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field observation wire current.
Proof.
  intros BINDINGS CALL STACK WELL CAPTURED RESERVED COPY_OWNER ORIGINAL PRIVATE DESTROY RECEIVED FIELDS METADATA PROTECTED INITIAL RUN NONNULL.
  destruct(gateway_return_cut backend ge(Internal f_host_call_objects)
    [Vptr callable callable_offset;Vptr output Ptrofs.zero;Vint Int.one](gateway_outcome_path_cont environment parameters)
    before world events(Returnstate value Kstop after)next ltac:(exact I)ltac:(cbn;lia)RUN)
    as(reading &suffix &returned &memory &current &EVENTS &HELPER &REST).
  assert(RETURNED_NONNULL:returned<>Vnullptr).
  { intro NULL;subst returned;apply NONNULL;eapply gateway_actual_outcome_path_null;exact REST. }
  destruct(gateway_actual_outcome_presentation backend ge python objects tuples decimal_float detached io stable thread_errno heap_allocation
    thread threads references metadata presentation(plug_cont(gateway_outcome_path_cont environment parameters)context)older held reserved captured
    protected source output Ptrofs.zero child child_offset callable callable_offset original copy
    (gateway_reference_temporary(gateway_reference_depth context)_copy)copy_ticket fields wires metadata_field observation wire
    before world reading returned memory current BINDINGS I STACK WELL CAPTURED RESERVED COPY_OWNER ORIGINAL PRIVATE DESTROY RECEIVED FIELDS METADATA
    ltac:(change(0+8<=18446744073709551616)%Z;lia)ltac:(change(Ptrofs.unsigned Ptrofs.zero)with 0%Z;exact PROTECTED)INITIAL HELPER RETURNED_NONNULL)
    as(final &object &offset &tuple &tuple_offset &callback_prefix &callback_suffix &mc &wc &mr &wr &observed
      &VALUE &CALLBACK_EVENTS &CALLBACK &FINAL_WELL &ENTRIES &NEXT &FINAL_CONTEXT &COPY_FINAL &FINAL_FIELDS &FINAL_METADATA &SNAPSHOT &BOUND).
  exists reading,suffix,returned,object,offset,memory,current,final.
  split;[exact EVENTS|]. split;[exact VALUE|]. split;[exact HELPER|]. split;[exact REST|]. split;[exact FINAL_WELL|].
  split;[exact ENTRIES|]. split;[exact NEXT|]. exact(conj FINAL_CONTEXT(conj COPY_FINAL(conj FINAL_FIELDS FINAL_METADATA))).
Qed.
