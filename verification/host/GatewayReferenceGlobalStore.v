(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual owning-global stores archive references without a fictitious DecRef. *)
From Stdlib Require Import List.
From compcert Require Import Maps Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceHistory
  GatewayReferenceAbandon GatewayReferenceOverwrite.
Import ListNotations.

Definition gateway_history_global_store_select {World Event}:gateway_history_selector World Event:=
  fun position first event last history=>
  match event,first with
  |gateway_source _,gateway_live(Returnstate value(Kcall(Some identifier)_ _ _ rest)_)_=>
    if Val.eq value Vnullptr then gateway_history_current gateway_reference_keep else
      gateway_history_current(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth rest)))
        (gateway_reference_temporary(gateway_reference_depth rest)identifier))
  |gateway_source _,gateway_live(State _ (Sassign(Evar global _)(Etempvar identifier _))continuation _ parameters _)_=>
    match parameters!identifier with
    |None=>gateway_history_current gateway_reference_unclassified
    |Some value=>if Val.eq value Vnullptr then gateway_history_clear(gateway_reference_global global)
      else gateway_history_assign(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
        (gateway_reference_global global)
    end
  |gateway_source _,gateway_live(State _ Sskip _ _ _ _)_=>gateway_history_current gateway_reference_keep
  |gateway_ambient,_|gateway_blocked,_|gateway_lost,_=>gateway_history_current gateway_reference_keep
  |_,_=>gateway_history_current gateway_reference_unclassified
  end.

Theorem gateway_history_actual_owned_global_store {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function global identifier pointer_type continuation environment parameters object offset before after world
    position ledger retired ticket:
  parameters!identifier=Some(Vptr object offset)->gateway_history_well_formed position ledger retired->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    ticket(Vptr object offset)->
  gateway_step backend ge
    (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))continuation
      environment parameters before)world)(gateway_source E0)
    (gateway_live(State function Sskip continuation environment parameters after)world)->
  exists next archived,
    gateway_history_execution backend ge gateway_history_global_store_select position
      (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))continuation
        environment parameters before)world)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}[gateway_source E0]
      (gateway_live(State function Sskip continuation environment parameters after)world)
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|} /\
    gateway_history_well_formed(S position)next archived /\
    gateway_reference_owns next(gateway_reference_global global)ticket(Vptr object offset) /\
    (forall value,gateway_history_total_count next archived value=gateway_history_total_count ledger retired value).
Proof.
  intros VALUE FORMED OWNED SOURCE.
  destruct(gateway_history_assign_owned position ledger retired
    (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    (gateway_reference_global global)ticket(Vptr object offset)FORMED OWNED)
    as[next[archived[APPLY[WELL[CAPTURED[COUNTS RETAINED]]]]]].
  assert(SELECT:@gateway_history_global_store_select World Event position
    (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))continuation
      environment parameters before)world)(gateway_source E0)
    (gateway_live(State function Sskip continuation environment parameters after)world)
    {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}=
    gateway_history_assign(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
      (gateway_reference_global global)).
  { unfold gateway_history_global_store_select;rewrite VALUE.
    destruct(Val.eq(Vptr object offset)Vnullptr);[discriminate|reflexivity]. }
  exists next,archived;split.
  - econstructor;[exact SOURCE|]. rewrite SELECT,APPLY;constructor.
  - exact(conj WELL(conj CAPTURED COUNTS)).
Qed.

Theorem gateway_history_actual_null_global_store {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function global identifier pointer_type continuation environment parameters before after world position ledger retired:
  parameters!identifier=Some Vnullptr->gateway_history_well_formed position ledger retired->
  gateway_step backend ge
    (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))continuation
      environment parameters before)world)(gateway_source E0)
    (gateway_live(State function Sskip continuation environment parameters after)world)->
  exists next archived,
    gateway_history_execution backend ge gateway_history_global_store_select position
      (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))continuation
        environment parameters before)world)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}[gateway_source E0]
      (gateway_live(State function Sskip continuation environment parameters after)world)
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|} /\
    gateway_history_well_formed(S position)next archived /\
    gateway_reference_take(gateway_reference_global global)(gateway_reference_entries next)=None /\
    (forall value,gateway_history_total_count next archived value=gateway_history_total_count ledger retired value).
Proof.
  intros VALUE FORMED SOURCE.
  destruct(gateway_history_clear_owned position ledger retired(gateway_reference_global global)FORMED)
    as[next[archived[APPLY[WELL[VACANT COUNTS]]]]].
  assert(SELECT:@gateway_history_global_store_select World Event position
    (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))continuation
      environment parameters before)world)(gateway_source E0)
    (gateway_live(State function Sskip continuation environment parameters after)world)
    {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}=
    gateway_history_clear(gateway_reference_global global)).
  { unfold gateway_history_global_store_select;rewrite VALUE.
    destruct(Val.eq Vnullptr Vnullptr);[reflexivity|contradiction]. }
  exists next,archived;split.
  - econstructor;[exact SOURCE|]. rewrite SELECT,APPLY;constructor.
  - exact(conj WELL(conj VACANT COUNTS)).
Qed.
