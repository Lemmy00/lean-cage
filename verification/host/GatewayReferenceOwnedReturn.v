(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A source return retains exact older caller entries and transfers
   its selected reference through real local cleanup and enclosing caller frames. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Events Ctypes Cop Clight.
Require Import LocalAccess CallContexts.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayObjectThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceExecution
  GatewayReferenceFrames GatewayReferenceMoves GatewayReferenceThreads GatewayReferenceContextReturns
  GatewayReferenceActivation GatewayReferenceNormalForm GatewayReferenceStackBound GatewayThreadInvariant GatewayReturnRuntime GatewayReadonly GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_context_return_entries {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)context
    python objects decimal_float io native stable base thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io native stable base thread_errno)
    (references:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    function identifier environment temporaries expression following pointer before world events actual after next initial ledger ticket held:
  is_call_cont context->call_cont following=Kstop->gateway_reference_temporary_expression expression=Some identifier->
  (forall memory,expression_value ge environment temporaries memory expression pointer)->
  (forall memory converted,sem_cast pointer(typeof expression)(fn_return function)memory=Some converted->converted=pointer)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth(plug_cont following context))identifier)ticket pointer->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth(plug_cont following context)))
    (gateway_reference_entries ledger)=None->
  gateway_reference_stack_bound context initial->
  gateway_reference_entries ledger=
    gateway_reference_entry ticket(gateway_reference_temporary(gateway_reference_depth(plug_cont following context))identifier)pointer::gateway_reference_entries initial->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_return_environment native base None environment before world->
  gateway_steps backend ge(gateway_live(State function(Sreturn(Some expression))following environment temporaries before)world)events
    (gateway_live(Returnstate actual Kstop after)next)->
  exists final,
    actual=pointer /\gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_plug(gateway_live(State function(Sreturn(Some expression))following environment temporaries before)world)context)
      (gateway_reference_valid ledger)events(gateway_plug(gateway_live(Returnstate actual Kstop after)next)context)
      (gateway_reference_valid final) /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))ticket pointer /\
    gateway_reference_place_value ge(plug_state(Returnstate actual Kstop after)context)
      (gateway_reference_result(gateway_reference_depth context))pointer /\
    gateway_reference_scope python objects decimal_float final held next /\base None after next /\Forall gateway_quiet_event events /\
    gateway_reference_result_entries context initial final ticket pointer /\
    gateway_reference_source_bound ge(plug_state(Returnstate actual Kstop after)context)final.
Proof.
  intros CALL STOP FORM EXPRESSION CAST FORMED OWNED VACANT STACK HEAD SCOPE ENV RUN.
  destruct(gateway_reference_context_source_return backend ge context function expression identifier following environment temporaries
    pointer before world events actual after next ledger ticket STOP FORM EXPRESSION CAST FORMED OWNED VACANT RUN)
    as[final[SAME[EXECUTION[MOVE[WELL[CAPTURED COUNTS]]]]]].
  destruct(gateway_reference_move_scope python objects decimal_float ledger
    (gateway_reference_temporary(gateway_reference_depth(plug_cont following context))identifier)
    (gateway_reference_result(gateway_reference_depth(plug_cont following context)))ticket pointer held world
    FORMED OWNED VACANT SCOPE)as[moved[APPLY[MOVED_WELL[MOVED_OWNED[MOVED_SCOPE OTHERS]]]]].
  rewrite MOVE in APPLY;injection APPLY as MATCH;subst moved.
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation
    python objects decimal_float references final held runtime)as SCOPED_RUNTIME.
  assert(READY:gateway_return_environment native
    (gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float final held))
    None environment before world).
  { split;[split;[exact(proj1 ENV)|exact MOVED_SCOPE]|exact(proj2 ENV)]. }
  destruct(gateway_actual_return_side backend ge io native stable _ thread_errno SCOPED_RUNTIME None function(Some expression)following
    environment temporaries before world events actual after next STOP READY RUN)as[[AFTER_SCOPE AFTER]QUIET].
  assert(DEPTH:gateway_reference_depth(plug_cont following context)=gateway_reference_depth context).
  { rewrite gateway_reference_depth_plug.
    pose proof(gateway_reference_call_cont_depth following)as SAME_DEPTH;rewrite STOP in SAME_DEPTH;cbn in SAME_DEPTH;lia. }
  exists final;split;[exact SAME|]. split.
  - eapply gateway_reference_context_execution_plugs;[exact CALL|exact EXECUTION].
  - split;[exact WELL|]. split;[rewrite<-DEPTH;exact CAPTURED|]. split.
    + rewrite SAME;apply gateway_reference_result_binding.
    + split;[exact AFTER|]. split;[exact AFTER_SCOPE|]. split;[exact QUIET|].
      destruct(gateway_reference_head_move ledger final(gateway_reference_entries initial)ticket
        (gateway_reference_temporary(gateway_reference_depth(plug_cont following context))identifier)
        (gateway_reference_result(gateway_reference_depth(plug_cont following context)))pointer HEAD MOVE)as[ENTRIES NEXT_COUNTER].
      rewrite DEPTH in ENTRIES;split;[exact ENTRIES|]. rewrite SAME.
      eapply gateway_reference_result_entries_bound;[exact STACK|exact ENTRIES].
Qed.
