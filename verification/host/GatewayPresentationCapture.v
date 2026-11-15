(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A returned SDK credit moves through the actual saved temporary
   into its real source holder. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Ctypes Clight.
Require Import CallContexts.
From HostGateway Require Import GatewayMachine GatewayPython GatewaySource GatewayContexts GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceFrames
  GatewayReferenceAccounting GatewayReferenceNormalForm GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceCapture GatewayReferenceActivation
  GatewayReferenceCaptureObservation GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_presentation_actual_capture {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float(property:mem->World->Prop)context parameters first destination tail pointer
    before world events value after next ledger ticket rest held reserved:
  is_call_cont context ->call_cont tail=Kstop ->gateway_ambient_closed backend property ->property before world ->first<>destination ->
  (forall memory current,property memory current->gateway_reference_scope python objects decimal_float ledger held current /\
    forall object,(count_occ Val.eq reserved object+gateway_reference_count ledger object<=python_native_strong(python current)object)%nat) ->
  gateway_reference_ledger_well_formed ledger ->
  gateway_reference_entries ledger=gateway_reference_entry ticket(gateway_reference_result(S(gateway_reference_depth context)))pointer::rest ->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)first)(gateway_reference_entries ledger)=None ->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)destination)(gateway_reference_entries ledger)=None ->
  gateway_steps backend ge(gateway_live(Returnstate pointer
    (gateway_reference_capture_cont GatewaySource.f_host_call_objects empty_env parameters first destination
      (Ctypes.Tpointer(Ctypes.Tstruct GatewaySource.__object Ctypes.noattr)Ctypes.noattr)tail)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  exists stored prefix suffix memory current,
    events=prefix++suffix /\property memory current /\gateway_reference_ledger_well_formed stored /\
    gateway_reference_entries stored=gateway_reference_entry ticket(gateway_reference_temporary(gateway_reference_depth context)destination)pointer::rest /\
    gateway_reference_next stored=gateway_reference_next ledger /\
    gateway_reference_scope python objects decimal_float stored held current /\
    (forall object,(count_occ Val.eq reserved object+gateway_reference_count stored object<=python_native_strong(python current)object)%nat) /\
    (forall object,gateway_reference_count stored object=gateway_reference_count ledger object) /\
    gateway_steps backend ge(gateway_live(Returnstate pointer
      (gateway_reference_capture_cont GatewaySource.f_host_call_objects empty_env parameters first destination
        (Ctypes.Tpointer(Ctypes.Tstruct GatewaySource.__object Ctypes.noattr)Ctypes.noattr)tail)before)world)prefix
      (gateway_live(State GatewaySource.f_host_call_objects Sskip tail empty_env
        (gateway_reference_capture_parameters parameters first destination pointer)memory)current) /\
    gateway_steps backend ge(gateway_live(State GatewaySource.f_host_call_objects Sskip tail empty_env
      (gateway_reference_capture_parameters parameters first destination pointer)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CALL STOP CLOSED INPUT DIFFERENT OBSERVATIONS WELL ENTRIES FIRST LAST RUN.
  assert(DEPTH:gateway_reference_depth(plug_cont tail context)=gateway_reference_depth context).
  { rewrite gateway_reference_depth_plug.
    pose proof(gateway_reference_call_cont_depth tail)as SAME;rewrite STOP in SAME;cbn in SAME;lia. }
  assert(OWNED:gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))ticket pointer).
  { rewrite DEPTH;unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity. }
  destruct(gateway_actual_context_capture_scope backend ge python objects decimal_float property context GatewaySource.f_host_call_objects
    empty_env parameters first destination(Ctypes.Tpointer(Ctypes.Tstruct GatewaySource.__object Ctypes.noattr)Ctypes.noattr)
    tail pointer before world events value after next ledger ticket held reserved CALL CLOSED INPUT DIFFERENT OBSERVATIONS WELL OWNED
    ltac:(rewrite DEPTH;exact FIRST)ltac:(rewrite DEPTH;exact LAST)RUN)
    as(stored &prefix &suffix &memory &current &EVENTS &GOOD &FORMED &OWNER &SCOPE &BUDGET &BOUND &COUNTS &MOVES &RETAINED &PREFIX &EXECUTION &SUFFIX).
  destruct MOVES as[returned[RETURN_MOVE STORE_MOVE]].
  rewrite DEPTH in RETURN_MOVE,STORE_MOVE.
  destruct(gateway_reference_head_move ledger returned rest ticket(gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_temporary(gateway_reference_depth context)first)pointer ENTRIES RETURN_MOVE)as[RETURNED_ENTRIES RETURNED_NEXT].
  destruct(gateway_reference_head_move returned stored rest ticket(gateway_reference_temporary(gateway_reference_depth context)first)
    (gateway_reference_temporary(gateway_reference_depth context)destination)pointer RETURNED_ENTRIES STORE_MOVE)as[FINAL_ENTRIES FINAL_NEXT].
  exists stored,prefix,suffix,memory,current.
  split;[exact EVENTS|]. split;[exact GOOD|]. split;[exact FORMED|]. split;[exact FINAL_ENTRIES|]. split;[congruence|].
  exact(conj SCOPE(conj BUDGET(conj COUNTS(conj PREFIX SUFFIX)))).
Qed.
