(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual caller return retains its moved reference and held graphs. *)
From Stdlib Require Import List.
From compcert Require Import Maps AST Values Memory Events Ctypes Cop Clight.
Require Import LocalAccess.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayObjectThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceExecution
  GatewayReferenceFrames GatewayReferenceMoves GatewayReferenceThreads GatewayReferenceReturnPath
  GatewayThreadInvariant GatewayReturnRuntime GatewayCallerReturns GatewayReadonly GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_caller_scope {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float io native stable base thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io native stable base thread_errno)
    (references:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    function destination environment temporaries expression following pointer before world events actual after next ledger ticket held:
  call_cont following=Kstop->gateway_reference_temporary_expression expression=Some destination->
  (forall memory,expression_value ge environment(PTree.set destination pointer temporaries)memory expression pointer)->
  (forall memory converted,sem_cast pointer(typeof expression)(fn_return function)memory=Some converted->converted=pointer)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth following)))ticket pointer->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth following)destination)
    (gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth following))
    (gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_return_environment native base None environment before world->
  gateway_steps backend ge
    (gateway_live(Returnstate pointer(Kcall(Some destination)function environment temporaries
      (Kseq(Sreturn(Some expression))following))before)world)events
    (gateway_live(Returnstate actual Kstop after)next)->
  exists final,
    actual=pointer /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(Returnstate pointer(Kcall(Some destination)function environment temporaries
        (Kseq(Sreturn(Some expression))following))before)world)(gateway_reference_valid ledger)events
      (gateway_live(Returnstate actual Kstop after)next)(gateway_reference_valid final) /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth following))ticket pointer /\
    gateway_reference_place_value ge(Returnstate actual Kstop after)
      (gateway_reference_result(gateway_reference_depth following))pointer /\
    gateway_reference_scope python objects decimal_float final held next /\base None after next /\
    Forall gateway_quiet_event events.
Proof.
  intros STOP FORM EXPRESSION CAST FORMED OWNED TEMP_FREE RESULT_FREE SCOPE ENV RUN.
  destruct(gateway_reference_actual_caller_result backend ge function destination environment temporaries expression following
    pointer before world events actual after next ledger ticket STOP FORM EXPRESSION CAST FORMED OWNED TEMP_FREE RESULT_FREE RUN)
    as[intermediate[final[SAME[EXECUTION[MOVE[RETURN[WELL[CAPTURED COUNTS]]]]]]]].
  destruct(gateway_reference_move_scope python objects decimal_float ledger
    (gateway_reference_result(S(gateway_reference_depth following)))
    (gateway_reference_temporary(gateway_reference_depth following)destination)ticket pointer held world
    FORMED OWNED TEMP_FREE SCOPE)as[moved[APPLY[MOVED_WELL[MOVED_OWNED[MOVED_SCOPE OTHERS]]]]].
  rewrite MOVE in APPLY;injection APPLY as MATCH;subst moved.
  assert(RESULT_VACANT:gateway_reference_take(gateway_reference_result(gateway_reference_depth following))
    (gateway_reference_entries intermediate)=None).
  { eapply(gateway_reference_move_keeps_vacant ledger
      (gateway_reference_result(S(gateway_reference_depth following)))
      (gateway_reference_temporary(gateway_reference_depth following)destination)
      (gateway_reference_result(gateway_reference_depth following))intermediate);
      [exact RESULT_FREE|discriminate|exact MOVE]. }
  destruct(gateway_reference_move_scope python objects decimal_float intermediate
    (gateway_reference_temporary(gateway_reference_depth following)destination)
    (gateway_reference_result(gateway_reference_depth following))ticket pointer held world
    MOVED_WELL MOVED_OWNED RESULT_VACANT MOVED_SCOPE)
    as[returned[APPLY[RETURN_WELL[RETURN_OWNED[RETURN_SCOPE REST]]]]].
  rewrite RETURN in APPLY;injection APPLY as MATCH;subst returned.
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation
    python objects decimal_float references final held runtime)as SCOPED_RUNTIME.
  assert(READY:gateway_return_environment native
    (gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float final held))
    None environment before world).
  { split;[split;[exact(proj1 ENV)|exact RETURN_SCOPE]|exact(proj2 ENV)]. }
  destruct(gateway_actual_caller_return_side backend ge io native stable _ thread_errno SCOPED_RUNTIME
    None function(Some destination)environment temporaries(Some expression)following before world events pointer actual after next
    STOP READY RUN)as[[AFTER_SCOPE AFTER]QUIET].
  exists final;split;[exact SAME|]. split;[exact EXECUTION|]. split;[exact WELL|]. split;[exact CAPTURED|]. split.
  - rewrite SAME.
    rewrite<-gateway_reference_call_cont_depth,STOP;apply gateway_reference_result_binding.
  - split;[exact AFTER|]. split;[exact AFTER_SCOPE|exact QUIET].
Qed.
