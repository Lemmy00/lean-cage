(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual Path callback retains the received dictionary and
   original JSON observation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewayImport GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueFrame GatewayContainerGraph GatewayGraphSnapshots GatewayObjectDiscipline GatewayObjectThreads GatewayThreadRuntime GatewayStreamInterface
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceStackBound GatewayReferenceNormalForm
  GatewayReferenceHeld GatewayReferenceThreads GatewayPresentationRuntime GatewayPresentationTrace GatewayPresentationCredits GatewayPresentationContext
  GatewayOwnedPresentation GatewayOutcomeFields GatewayOutcomeMetadata GatewayOutcomePresentationViews.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_outcome_presentation {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples decimal_float detached io stable thread_errno heap_allocation
    (thread:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_reference_runtime backend python objects)
    (metadata:gateway_presentation_reference_runtime backend python objects tuples)
    (presentation:gateway_presentation_runtime backend python objects tuples(fun current object=>gateway_native_private(python current)object))
    context older held reserved captured protected source array displacement child child_offset callable callable_offset
    original copy copy_owner copy_ticket fields wires metadata_field observation wire before world events value after next:
  gateway_presentation_bindings ge ->is_call_cont context ->gateway_reference_stack_bound context older ->
  gateway_reference_ledger_well_formed older ->In captured held ->In(Vptr callable callable_offset)reserved ->
  gateway_reference_owns older copy_owner copy_ticket copy ->
  gateway_object_values(objects world)original=Some(gateway_dict_object fields) ->
  gateway_private_tree(objects world)original ->gateway_destructible(objects world)original ->
  gateway_dictionary_heap decimal_float(objects world)fields wires ->
  gateway_outcome_fields_view python objects decimal_float copy fields wires world ->
  gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field observation wire world ->
  (Ptrofs.unsigned displacement+8<=Ptrofs.modulus)%Z ->
  (forall position,(Ptrofs.unsigned displacement<=position<Ptrofs.unsigned displacement+8)%Z->protected array position) ->
  gateway_presentation_context python objects decimal_float older held reserved captured protected source array displacement
    (Vptr child child_offset)before world ->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_call_objects)
    [Vptr callable callable_offset;Vptr array displacement;Vint Int.one]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists final object offset tuple tuple_offset prefix suffix callback_memory callback_world returned_memory returned_world observed,
    value=Vptr object offset /\events=prefix++gateway_primitive observed::suffix /\
    gateway_presentation_operation backend gateway_presentation_call[Vptr callable callable_offset;Vptr tuple tuple_offset]
      callback_memory callback_world value returned_memory returned_world observed /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=gateway_reference_entry(S(S(gateway_reference_next older)))
      (gateway_reference_result(gateway_reference_depth context))value::gateway_reference_entries older /\
    gateway_reference_next final=S(S(S(gateway_reference_next older))) /\
    gateway_presentation_context python objects decimal_float final held reserved captured protected source array displacement
      (Vptr child child_offset)after next /\
    gateway_reference_owns final copy_owner copy_ticket copy /\
    gateway_outcome_fields_view python objects decimal_float copy fields wires next /\
    gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field observation wire next /\
    gateway_graph_snapshot(objects world)(objects next)copy /\
    gateway_reference_source_bound ge(Returnstate value context after)final.
Proof.
  intros BINDINGS CALL STACK WELL CAPTURED RESERVED COPY_TICKET ORIGINAL PRIVATE DESTROY RECEIVED FIELDS METADATA NOWRAP PROTECTED INITIAL RUN NONNULL.
  pose proof(gateway_outcome_fields_value _ _ _ _ _ _ _ FIELDS)as COPY_VALUE.
  destruct(gateway_graph_from_children(objects world)copy(gateway_dict_object fields)gateway_dict_kind COPY_VALUE
    (gateway_outcome_fields_private _ _ _ _ _ _ _ FIELDS)eq_refl ltac:(unfold gateway_destructor_kind;tauto)
    ltac:(intros child_pointer MEMBER;unfold gateway_object_children,gateway_dictionary_children in MEMBER;
      apply in_flat_map in MEMBER;destruct MEMBER as[field[MEMBER[KEY|[ITEM|EMPTY]]]];
      [subst child_pointer;eapply gateway_outcome_child_subtree;[exact ORIGINAL|exact MEMBER|left;reflexivity|exact PRIVATE|exact DESTROY]|
       subst child_pointer;eapply gateway_outcome_child_subtree;[exact ORIGINAL|exact MEMBER|right;reflexivity|exact PRIVATE|exact DESTROY]|contradiction]))
    as[COPY_PRIVATE COPY_DESTROY].
  set(copy_wire:=LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields wires)).
  assert(COPY_WIRE:gateway_value_heap decimal_float(objects world)copy copy_wire)
    by(eapply gateway_heap_dictionary;[exact COPY_VALUE|exact RECEIVED]).
  set(copy_snapshot:={|gateway_held_ticket:=copy_ticket;gateway_held_object:=copy;
    gateway_held_view:=gateway_held_graph_value copy_wire(objects world)|}).
  assert(AUGMENTED:gateway_reference_scope python objects decimal_float older(copy_snapshot::held)world).
  { destruct(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ INITIAL)as[FIT HELD].
    split;[exact FIT|]. constructor;[|exact HELD].
    split;[exists copy_owner;exact COPY_TICKET|]. split;[exact COPY_PRIVATE|]. split;[exact COPY_DESTROY|].
    exact(conj COPY_WIRE(conj COPY_DESTROY(gateway_graph_snapshot_refl _ _))). }
  assert(AUGMENTED_CONTEXT:gateway_presentation_context python objects decimal_float older(copy_snapshot::held)reserved captured protected source
    array displacement(Vptr child child_offset)before world)by(eapply gateway_presentation_context_held;eassumption).
  destruct(gateway_actual_owned_presentation backend ge python objects tuples decimal_float detached io stable thread_errno heap_allocation
    thread threads references metadata presentation context older(copy_snapshot::held)reserved captured protected source array displacement child child_offset
    callable callable_offset before world events value after next BINDINGS CALL STACK WELL ltac:(right;exact CAPTURED)RESERVED NOWRAP PROTECTED
    AUGMENTED_CONTEXT RUN NONNULL)
    as(final &object &offset &tuple &tuple_offset &prefix &suffix &mc &wc &mr &wr &observed &VALUE &EVENTS &OPERATION &FINAL_WELL &ENTRIES &NEXT &FINAL_CONTEXT &BOUND).
  pose proof(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ FINAL_CONTEXT)as[FIT HELD].
  inversion HELD as[|captured_copy rest COPY_VIEW REST];subst captured_copy rest.
  destruct COPY_VIEW as[[owner OWNED][FINAL_PRIVATE[FINAL_DESTROY[FINAL_WIRE[OLD_DESTROY SNAPSHOT]]]]].
  change(gateway_reference_owns final owner copy_ticket copy)in OWNED.
  change(gateway_private_tree(objects next)copy)in FINAL_PRIVATE.
  change(gateway_graph_snapshot(objects world)(objects next)copy)in SNAPSHOT.
  assert(COPY_POSITIVE:(0<python_native_strong(python next)copy)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(FIT copy);lia. }
  assert(GRAPH_FRAME:gateway_graph_region_frame(objects world)(objects next)copy).
  { intros pointer REACHED;split.
    - intros old OLD;rewrite SNAPSHOT by exact REACHED;exact OLD.
    - apply FINAL_PRIVATE;eapply gateway_graph_snapshot_forward;[exact SNAPSHOT|exact REACHED]. }
  exists final,object,offset,tuple,tuple_offset,prefix,suffix,mc,wc,mr,wr,observed.
  split;[exact VALUE|]. split;[exact EVENTS|]. split;[exact OPERATION|]. split;[exact FINAL_WELL|].
  split;[exact ENTRIES|]. split;[exact NEXT|]. split.
  - eapply gateway_presentation_context_held;[exact FINAL_CONTEXT|exact(conj FIT REST)].
  - split.
    + unfold gateway_reference_owns;rewrite ENTRIES;right;exact COPY_TICKET.
    + split;[eapply gateway_outcome_fields_snapshot;eassumption|]. split;
        [eapply gateway_outcome_metadata_snapshot;eassumption|exact(conj SNAPSHOT BOUND)].
Qed.
