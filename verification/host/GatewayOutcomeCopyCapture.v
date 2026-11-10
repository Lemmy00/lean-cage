(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original copy credit reaches _copy on the same older caller stack. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayObjectThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceActivation GatewayReferenceAccounting GatewayReferenceNormalForm GatewayReferenceStackBound
  GatewayReferenceCapture GatewayReferenceFrames GatewayReferenceExecution GatewayReferenceMoves GatewayReferenceThreads
  GatewayOutcomeCopySource GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_reference_stack_current_vacant context ledger identifier:
  gateway_reference_stack_bound context ledger->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)identifier)(gateway_reference_entries ledger)=None.
Proof.
  intros STACK;apply gateway_reference_take_none;intros entry MEMBER OWNER.
  destruct(STACK entry MEMBER)as[invocation[name[PLACE SAVED]]].
  rewrite PLACE in OWNER;inversion OWNER;subst invocation name.
  rewrite gateway_reference_saved_above in SAVED by lia;discriminate.
Qed.

Theorem gateway_actual_outcome_copy_capture_with_property {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float(property:mem->World->Prop)context environment parameters pointer
    before world events value after next older ledger ticket held reserved:
  gateway_ambient_closed backend property->property before world->
  (forall memory current,property memory current->
    gateway_reference_scope python objects decimal_float ledger held current /\
    forall object,(count_occ Val.eq reserved object+gateway_reference_count ledger object<=
      python_native_strong(python current)object)%nat)->
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry ticket
    (gateway_reference_result(S(gateway_reference_depth context)))pointer::gateway_reference_entries older->
  gateway_steps backend ge
    (gateway_live(Returnstate pointer(plug_cont(gateway_outcome_copy_cont environment parameters)context)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists stored prefix suffix memory current,
    events=prefix++suffix /\property memory current /\gateway_reference_ledger_well_formed stored /\
    gateway_reference_entries stored=gateway_reference_entry ticket
      (gateway_reference_temporary(gateway_reference_depth context)_copy)pointer::gateway_reference_entries older /\
    gateway_reference_scope python objects decimal_float stored held current /\
    (forall object,(count_occ Val.eq reserved object+gateway_reference_count stored object<=
      python_native_strong(python current)object)%nat) /\
    gateway_reference_source_bound ge
      (State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters pointer)memory)stored /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(Returnstate pointer(plug_cont(gateway_outcome_copy_cont environment parameters)context)before)world)
      (gateway_reference_valid ledger)prefix
      (gateway_live(State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters pointer)memory)current)(gateway_reference_valid stored) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters pointer)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED INPUT OBSERVATIONS STACK WELL ENTRIES RUN.
  assert(OWNED:gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth context)))ticket pointer).
  { unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity. }
  assert(VACANT:forall identifier,
    gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)identifier)(gateway_reference_entries ledger)=None).
  { intro identifier;rewrite ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
    destruct(gateway_reference_place_eq(gateway_reference_temporary(gateway_reference_depth context)identifier)
      (gateway_reference_result(S(gateway_reference_depth context))));[discriminate|].
    rewrite(gateway_reference_stack_current_vacant context older identifier STACK);reflexivity. }
  destruct(gateway_actual_returned_reference_capture backend ge property f_host_outcome_from environment parameters _t'20 _copy
    (tptr(Tstruct __object noattr))(Kseq gateway_outcome_after_copy context)pointer before world events value after next ledger ticket
    CLOSED INPUT ltac:(discriminate)WELL OWNED(VACANT _t'20)(VACANT _copy)RUN)
    as(returned &stored &prefix &suffix &memory &current &EVENTS &CURRENT &EXECUTION &RETURN_MOVE &STORE_MOVE &
      FINAL_WELL &FINAL_OWNED &FINAL_BINDING &COUNTS &SUFFIX).
  destruct(OBSERVATIONS memory current CURRENT)as[SCOPE BUDGET].
  destruct(gateway_reference_move_scope python objects decimal_float ledger(gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_temporary(gateway_reference_depth context)_t'20)ticket pointer held current
    WELL OWNED(VACANT _t'20)SCOPE)
    as(moved &MOVE &MOVED_WELL &MOVED_OWNED &MOVED_SCOPE &MOVED_COUNTS &RETAINED).
  change(gateway_reference_apply(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_temporary(gateway_reference_depth context)_t'20))(gateway_reference_valid ledger)=gateway_reference_valid returned)in RETURN_MOVE.
  rewrite RETURN_MOVE in MOVE;injection MOVE as SAME;subst moved.
  assert(STORE_VACANT:gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)_copy)(gateway_reference_entries returned)=None).
  { eapply(gateway_reference_move_keeps_vacant ledger(gateway_reference_result(S(gateway_reference_depth context)))
      (gateway_reference_temporary(gateway_reference_depth context)_t'20)
      (gateway_reference_temporary(gateway_reference_depth context)_copy)returned);
      [apply VACANT|discriminate|exact RETURN_MOVE]. }
  destruct(gateway_reference_move_scope python objects decimal_float returned
    (gateway_reference_temporary(gateway_reference_depth context)_t'20)
    (gateway_reference_temporary(gateway_reference_depth context)_copy)ticket pointer held current
    MOVED_WELL MOVED_OWNED STORE_VACANT MOVED_SCOPE)
    as(stored_again &MOVE &STORED_WELL &STORED_OWNED &STORED_SCOPE &STORED_COUNTS &STORED_RETAINED).
  change(gateway_reference_apply(gateway_reference_move(gateway_reference_temporary(gateway_reference_depth context)_t'20)
    (gateway_reference_temporary(gateway_reference_depth context)_copy))(gateway_reference_valid returned)=gateway_reference_valid stored)in STORE_MOVE.
  rewrite STORE_MOVE in MOVE;injection MOVE as SAME;subst stored_again.
  pose proof(proj1(gateway_reference_head_move ledger returned(gateway_reference_entries older)ticket
    (gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_temporary(gateway_reference_depth context)_t'20)pointer ENTRIES RETURN_MOVE))as RETURNED_ENTRIES.
  pose proof(proj1(gateway_reference_head_move returned stored(gateway_reference_entries older)ticket
    (gateway_reference_temporary(gateway_reference_depth context)_t'20)
    (gateway_reference_temporary(gateway_reference_depth context)_copy)pointer RETURNED_ENTRIES STORE_MOVE))as STORED_ENTRIES.
  exists stored,prefix,suffix,memory,current.
  split;[exact EVENTS|]. split;[exact CURRENT|]. split;[exact FINAL_WELL|]. split;[exact STORED_ENTRIES|]. split;[exact STORED_SCOPE|]. split.
  - intro object;rewrite COUNTS;apply BUDGET.
  - split.
    + intros entry MEMBER;rewrite STORED_ENTRIES in MEMBER;destruct MEMBER as[SAME|MEMBER].
      * subst entry;exact FINAL_BINDING.
      * exact(gateway_reference_stack_local_bound ge context older(Kseq gateway_outcome_after_copy Kstop)STACK
          f_host_outcome_from Sskip environment(gateway_outcome_copied_parameters parameters pointer)memory entry MEMBER).
    + split;assumption.
Qed.

Theorem gateway_actual_outcome_copy_capture {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float(property:mem->World->Prop)context environment parameters pointer
    before world events value after next older ledger ticket held reserved:
  gateway_ambient_closed backend property->property before world->
  (forall memory current,property memory current->
    gateway_reference_scope python objects decimal_float ledger held current /\
    forall object,(count_occ Val.eq reserved object+gateway_reference_count ledger object<=
      python_native_strong(python current)object)%nat)->
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry ticket
    (gateway_reference_result(S(gateway_reference_depth context)))pointer::gateway_reference_entries older->
  gateway_steps backend ge
    (gateway_live(Returnstate pointer(plug_cont(gateway_outcome_copy_cont environment parameters)context)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists stored prefix suffix memory current,
    events=prefix++suffix /\gateway_reference_ledger_well_formed stored /\
    gateway_reference_entries stored=gateway_reference_entry ticket
      (gateway_reference_temporary(gateway_reference_depth context)_copy)pointer::gateway_reference_entries older /\
    gateway_reference_scope python objects decimal_float stored held current /\
    (forall object,(count_occ Val.eq reserved object+gateway_reference_count stored object<=
      python_native_strong(python current)object)%nat) /\
    gateway_reference_source_bound ge
      (State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters pointer)memory)stored /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(Returnstate pointer(plug_cont(gateway_outcome_copy_cont environment parameters)context)before)world)
      (gateway_reference_valid ledger)prefix
      (gateway_live(State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters pointer)memory)current)(gateway_reference_valid stored) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters pointer)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED INPUT OBSERVATIONS STACK WELL ENTRIES RUN.
  destruct(gateway_actual_outcome_copy_capture_with_property backend ge python objects decimal_float property context environment parameters pointer
    before world events value after next older ledger ticket held reserved CLOSED INPUT OBSERVATIONS STACK WELL ENTRIES RUN)
    as(stored &prefix &suffix &memory &current &EVENTS &CURRENT &FORMED &FINAL_ENTRIES &SCOPE &BUDGET &BOUND &EXECUTION &SUFFIX).
  exists stored,prefix,suffix,memory,current;
    exact(conj EVENTS(conj FORMED(conj FINAL_ENTRIES(conj SCOPE(conj BUDGET(conj BOUND(conj EXECUTION SUFFIX))))))).
Qed.
