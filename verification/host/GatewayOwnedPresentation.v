(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The complete actual tuple helper returns the observed callback
   result with its own source credit. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectDiscipline GatewayObjectThreads GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceStackBound GatewayReferenceNormalForm
  GatewayReferenceHeld GatewayReferenceThreads GatewayPresentationRuntime GatewayPresentationTrace GatewayPresentationCredits
  GatewayPresentationContext GatewayPresentationEntry GatewayPresentationOwnedPrefix GatewayPresentationOwnedReturn.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_owned_presentation {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples decimal_float detached io stable thread_errno heap_allocation
    (thread:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_reference_runtime backend python objects)
    (metadata:gateway_presentation_reference_runtime backend python objects tuples)
    (presentation:gateway_presentation_runtime backend python objects tuples(fun current object=>gateway_native_private(python current)object))
    context older held reserved captured protected source array displacement child child_offset callable callable_offset
    before world events value after next:
  gateway_presentation_bindings ge ->is_call_cont context ->gateway_reference_stack_bound context older ->
  gateway_reference_ledger_well_formed older ->In captured held ->In(Vptr callable callable_offset)reserved ->
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
    gateway_reference_source_bound ge(Returnstate value context after)final.
Proof.
  intros BINDINGS CALL STACK WELL CAPTURED RESERVED NOWRAP PROTECTED INITIAL RUN NONNULL.
  assert(CLOSED:gateway_ambient_closed backend(gateway_presentation_context python objects decimal_float older held reserved captured
    protected source array displacement(Vptr child child_offset))).
  { exact(gateway_presentation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      thread threads older held reserved captured protected source array displacement(Vptr child child_offset)CAPTURED PROTECTED). }
  destruct(gateway_actual_presentation_entry backend ge _ (Vptr callable callable_offset)(Vptr array displacement)
    before world events value after next CLOSED INITIAL RUN)
    as(pe &re &me &we &parameters &EVENTSE &ENTRY &READY &CALLABLE &ARRAY &COUNT &BODY).
  destruct(gateway_actual_owned_presentation_prefix backend ge python objects tuples decimal_float detached io stable thread_errno heap_allocation
    thread threads references metadata presentation context older held reserved captured protected source parameters array displacement child child_offset
    callable callable_offset me we re value after next BINDINGS CALL STACK WELL CAPTURED COUNT ARRAY CALLABLE NOWRAP PROTECTED READY BODY NONNULL)
    as(tuple &tuple_offset &ledger &selected &pp &rp &mp &wp &EVENTSP &LEDGER_WELL &ENTRIES &NEXT &ARGUMENTS &SELECTED_CALLABLE &INSTALLED &PREFIX &REST).
  assert(HELD_BELOW:forall current,In current held->(gateway_held_ticket current<gateway_reference_next older)%nat).
  { intros current MEMBER.
    destruct(proj1(Forall_forall _ _)(proj2(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ INITIAL))current MEMBER)
      as[[place OWNED]HELD_VIEW].
    pose proof(proj2(proj2 WELL))as LIMIT;apply Forall_forall with
      (x:=gateway_reference_entry(gateway_held_ticket current)place(gateway_held_object current))in LIMIT;[exact LIMIT|exact OWNED]. }
  destruct(gateway_actual_owned_presentation_return backend ge python objects tuples decimal_float detached io stable thread_errno heap_allocation
    thread threads presentation context older ledger held reserved captured protected source selected array displacement child child_offset callable callable_offset
    tuple tuple_offset(gateway_reference_next older)mp wp rp value after next BINDINGS CALL STACK LEDGER_WELL CAPTURED RESERVED HELD_BELOW
    ENTRIES ARGUMENTS SELECTED_CALLABLE PROTECTED INSTALLED REST NONNULL)
    as(final &object &offset &pc &rc &mc &wc &mr &wr &observed &VALUE &EVENTSC &OPERATION &FINAL_WELL &FINAL_ENTRIES &FINAL_NEXT &FINAL_CONTEXT &FINAL_BOUND).
  exists final,object,offset,tuple,tuple_offset,(pe++pp++pc),rc,mc,wc,mr,wr,observed.
  split;[exact VALUE|]. split.
  - rewrite EVENTSE,EVENTSP,EVENTSC;repeat rewrite<-app_assoc;reflexivity.
  - split;[exact OPERATION|]. split;[exact FINAL_WELL|]. split;[rewrite NEXT in FINAL_ENTRIES;exact FINAL_ENTRIES|].
    split;[congruence|exact(conj FINAL_CONTEXT FINAL_BOUND)].
Qed.
