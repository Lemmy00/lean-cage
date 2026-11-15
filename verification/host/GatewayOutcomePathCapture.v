(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The callback-result credit is captured by the real Outcome
   _path assignment. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayContexts GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceFrames
  GatewayReferenceActivation GatewayReferenceAccounting GatewayReferenceNormalForm GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceCapture
  GatewayReferenceCaptureObservation GatewayOutcomeOutputSource GatewayOutcomeConstruction GatewayFramedRuntime.
Import ListNotations.

Definition gateway_outcome_path_captured parameters pointer:=gateway_reference_capture_parameters parameters _t'22 _path pointer.
Definition gateway_outcome_after_path_capture:=Kseq gateway_outcome_path_after_call(Kseq gateway_outcome_allocation_tail Kstop).

Theorem gateway_actual_outcome_path_capture {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float(property:mem->World->Prop)context environment parameters pointer
    before world events value after next ledger ticket tail held reserved:
  is_call_cont context ->gateway_ambient_closed backend property ->property before world ->
  (forall memory current,property memory current->gateway_reference_scope python objects decimal_float ledger held current /\
    forall object,(count_occ Val.eq reserved object+gateway_reference_count ledger object<=python_native_strong(python current)object)%nat) ->
  gateway_reference_ledger_well_formed ledger ->
  gateway_reference_entries ledger=gateway_reference_entry ticket(gateway_reference_result(S(gateway_reference_depth context)))pointer::tail ->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)_t'22)(gateway_reference_entries ledger)=None ->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)_path)(gateway_reference_entries ledger)=None ->
  gateway_steps backend ge(gateway_live(Returnstate pointer(gateway_outcome_path_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  exists stored prefix suffix memory current,
    events=prefix++suffix /\property memory current /\gateway_reference_ledger_well_formed stored /\
    gateway_reference_entries stored=gateway_reference_entry ticket(gateway_reference_temporary(gateway_reference_depth context)_path)pointer::tail /\
    gateway_reference_next stored=gateway_reference_next ledger /\
    gateway_reference_scope python objects decimal_float stored held current /\
    (forall object,(count_occ Val.eq reserved object+gateway_reference_count stored object<=python_native_strong(python current)object)%nat) /\
    (forall object,gateway_reference_count stored object=gateway_reference_count ledger object) /\
    gateway_steps backend ge(gateway_live(Returnstate pointer(gateway_outcome_path_cont environment parameters)before)world)prefix
      (gateway_live(State f_host_outcome_from Sskip gateway_outcome_after_path_capture environment
        (gateway_outcome_path_captured parameters pointer)memory)current) /\
    gateway_steps backend ge(gateway_live(State f_host_outcome_from Sskip gateway_outcome_after_path_capture environment
      (gateway_outcome_path_captured parameters pointer)memory)current)suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CALL CLOSED INPUT OBSERVATIONS WELL ENTRIES FIRST LAST RUN.
  destruct(gateway_actual_context_capture_scope backend ge python objects decimal_float property context f_host_outcome_from environment
    parameters _t'22 _path(tptr(Tstruct __object noattr))gateway_outcome_after_path_capture pointer before world events value after next
    ledger ticket held reserved CALL CLOSED INPUT ltac:(discriminate)OBSERVATIONS WELL
    ltac:(unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity)FIRST LAST RUN)
    as(stored &prefix &suffix &memory &current &EVENTS &GOOD &FORMED &OWNER &SCOPE &BUDGET &BOUND &COUNTS &MOVES &RETAINED &PREFIX &EXECUTION &SUFFIX).
  destruct MOVES as[returned[RETURN_MOVE STORE_MOVE]].
  change(gateway_reference_apply(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_temporary(gateway_reference_depth context)_t'22))(gateway_reference_valid ledger)=gateway_reference_valid returned)in RETURN_MOVE.
  change(gateway_reference_apply(gateway_reference_move(gateway_reference_temporary(gateway_reference_depth context)_t'22)
    (gateway_reference_temporary(gateway_reference_depth context)_path))(gateway_reference_valid returned)=gateway_reference_valid stored)in STORE_MOVE.
  destruct(gateway_reference_head_move ledger returned tail ticket(gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_temporary(gateway_reference_depth context)_t'22)pointer ENTRIES RETURN_MOVE)as[RETURNED_ENTRIES RETURNED_NEXT].
  destruct(gateway_reference_head_move returned stored tail ticket(gateway_reference_temporary(gateway_reference_depth context)_t'22)
    (gateway_reference_temporary(gateway_reference_depth context)_path)pointer RETURNED_ENTRIES STORE_MOVE)as[FINAL_ENTRIES FINAL_NEXT].
  exists stored,prefix,suffix,memory,current.
  split;[exact EVENTS|]. split;[exact GOOD|]. split;[exact FORMED|]. split;[exact FINAL_ENTRIES|]. split;[congruence|].
  exact(conj SCOPE(conj BUDGET(conj COUNTS(conj PREFIX SUFFIX)))).
Qed.
