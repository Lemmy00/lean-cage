(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual callee captures keep the same aggregate source reference scope. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Ctypes Clight.
Require Import CallContexts.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferencePlaces GatewayReferenceMoves GatewayReferenceFrames GatewayReferenceExecution GatewayReferenceThreads GatewayReferenceContextCapture
  GatewayReferenceCapture GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_context_capture_scope {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float(property:mem->World->Prop)context function environment parameters identifier destination ty tail pointer
    before world events value after next ledger ticket held reserved:
  is_call_cont context->gateway_ambient_closed backend property->property before world->identifier<>destination->
  (forall memory current,property memory current->gateway_reference_scope python objects decimal_float ledger held current /\
    forall object,(count_occ Val.eq reserved object+gateway_reference_count ledger object<=python_native_strong(python current)object)%nat)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))ticket pointer->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)(gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)(gateway_reference_entries ledger)=None->
  gateway_steps backend ge(gateway_live(Returnstate pointer
    (gateway_reference_capture_cont function environment parameters identifier destination ty tail)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists stored prefix suffix memory current,
    events=prefix++suffix /\property memory current /\gateway_reference_ledger_well_formed stored /\
    gateway_reference_owns stored(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)ticket pointer /\
    gateway_reference_scope python objects decimal_float stored held current /\
    (forall object,(count_occ Val.eq reserved object+gateway_reference_count stored object<=python_native_strong(python current)object)%nat) /\
    gateway_reference_place_value ge(plug_state(State function Sskip tail environment
      (gateway_reference_capture_parameters parameters identifier destination pointer)memory)context)
      (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)pointer /\
    (forall object,gateway_reference_count stored object=gateway_reference_count ledger object) /\
    (exists returned,
      gateway_reference_apply(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))
        (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier))(gateway_reference_valid ledger)=gateway_reference_valid returned /\
      gateway_reference_apply(gateway_reference_move(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)
        (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination))(gateway_reference_valid returned)=gateway_reference_valid stored) /\
    (forall place other object,other<>ticket->gateway_reference_owns ledger place other object->gateway_reference_owns stored place other object) /\
    gateway_steps backend ge(gateway_live(Returnstate pointer
      (gateway_reference_capture_cont function environment parameters identifier destination ty tail)before)world)prefix
      (gateway_live(State function Sskip tail environment(gateway_reference_capture_parameters parameters identifier destination pointer)memory)current) /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (GatewayContexts.gateway_plug(gateway_live(Returnstate pointer
        (gateway_reference_capture_cont function environment parameters identifier destination ty tail)before)world)context)
      (gateway_reference_valid ledger)prefix
      (GatewayContexts.gateway_plug(gateway_live(State function Sskip tail environment
        (gateway_reference_capture_parameters parameters identifier destination pointer)memory)current)context)(gateway_reference_valid stored) /\
    gateway_steps backend ge(gateway_live(State function Sskip tail environment
      (gateway_reference_capture_parameters parameters identifier destination pointer)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CALL CLOSED INPUT DIFFERENT OBSERVATIONS WELL OWNED FIRST_VACANT LAST_VACANT RUN.
  destruct(gateway_actual_context_reference_capture backend ge property context function environment parameters identifier destination ty tail pointer
    before world events value after next ledger ticket CALL CLOSED INPUT DIFFERENT WELL OWNED FIRST_VACANT LAST_VACANT RUN)
    as(returned &stored &prefix &suffix &memory &current &EVENTS &CURRENT &PREFIX &EXECUTION &RETURN_MOVE &STORE_MOVE &
      STORED_WELL &STORED_OWNED &BOUND &COUNTS &SUFFIX).
  destruct(OBSERVATIONS memory current CURRENT)as[SCOPE BUDGET].
  destruct(gateway_reference_move_scope python objects decimal_float ledger
    (gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))
    (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)ticket pointer held current
    WELL OWNED FIRST_VACANT SCOPE)
    as(moved &MOVE &MOVED_WELL &MOVED_OWNED &MOVED_SCOPE &MOVED_COUNTS &RETAINED).
  rewrite RETURN_MOVE in MOVE;injection MOVE as SAME;subst moved.
  assert(STORE_VACANT:gateway_reference_take(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)
    (gateway_reference_entries returned)=None).
  { eapply(gateway_reference_move_keeps_vacant ledger(gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))
      (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)
      (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)returned);
      [exact LAST_VACANT|congruence|exact RETURN_MOVE]. }
  destruct(gateway_reference_move_scope python objects decimal_float returned
    (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)
    (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)ticket pointer held current
    MOVED_WELL MOVED_OWNED STORE_VACANT MOVED_SCOPE)
    as(stored_again &MOVE &FORMED &FINAL_OWNED &FINAL_SCOPE &FINAL_COUNTS &FINAL_RETAINED).
  rewrite STORE_MOVE in MOVE;injection MOVE as SAME;subst stored_again.
  exists stored,prefix,suffix,memory,current.
  split;[exact EVENTS|]. split;[exact CURRENT|]. split;[exact STORED_WELL|]. split;[exact STORED_OWNED|]. split;[exact FINAL_SCOPE|]. split.
  - intro object;rewrite COUNTS;apply BUDGET.
  - split;[exact BOUND|]. split;[exact COUNTS|]. split;[exists returned;split;assumption|]. split.
    + intros place other object OTHER OLD;apply FINAL_RETAINED;[exact OTHER|apply RETAINED;assumption].
    + exact(conj PREFIX(conj EXECUTION SUFFIX)).
Qed.
