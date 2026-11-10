(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source moves retain aliased held references. *)
From Stdlib Require Import List PeanoNat Sorting.Permutation.
From compcert Require Import Values Memory Events Clight.
From HostGateway Require Import GatewayMachine GatewayObjectThreads GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting
  GatewayReferenceFrames GatewayReferenceExecution GatewayReferenceHeld GatewayReferenceRetained GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_reference_owned_ticket_unique ledger owner ticket pointer place value:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger owner ticket pointer->
  gateway_reference_owns ledger place ticket value->place=owner /\value=pointer.
Proof.
  intros FORMED FIRST SECOND.
  destruct(gateway_reference_take_owned _ _ _ _ FORMED FIRST)as[remaining TAKE].
  destruct(gateway_reference_take_nodup gateway_reference_ticket _ _ _ _ TAKE(proj1 FORMED))as[UNIQUE ABSENT].
  pose proof(gateway_reference_take_permutation _ _ _ _ TAKE)as ORDER.
  apply(Permutation_in _ ORDER)in SECOND.
  destruct SECOND as[SAME|MEMBER].
  - injection SAME;intros;split;congruence.
  - exfalso;apply ABSENT;apply in_map_iff.
    exists{|gateway_reference_ticket:=ticket;gateway_reference_owner:=place;gateway_reference_pointer:=value|};
      split;[reflexivity|exact MEMBER].
Qed.

Theorem gateway_reference_move_scope {World}python objects decimal_float ledger from to ticket pointer held world:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger from ticket pointer->
  gateway_reference_take to(gateway_reference_entries ledger)=None->
  @gateway_reference_scope World python objects decimal_float ledger held world->
  exists next,
    gateway_reference_apply(gateway_reference_move from to)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\gateway_reference_ledger_well_formed next /\
    gateway_reference_owns next to ticket pointer /\
    gateway_reference_scope python objects decimal_float next held world /\
    (forall value,gateway_reference_count next value=gateway_reference_count ledger value) /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
      gateway_reference_owns next place other value).
Proof.
  intros FORMED OWNED VACANT[FIT HELD].
  destruct(gateway_reference_move_selected ledger from to ticket pointer FORMED OWNED)
    as[next[MOVE[WELL[CAPTURED[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    exact(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER OWNER).
  - assert(NEXT_FIT:gateway_reference_counts_fit next(python world)).
    { intro value;rewrite COUNTS;apply FIT. }
    exists next;split;[exact MOVE|]. split;[exact WELL|]. split;[exact CAPTURED|]. split.
    + split;[exact NEXT_FIT|].
      eapply(gateway_reference_held_frame python objects decimal_float ledger next held world world);
        [exact HELD|exact FIT|exact NEXT_FIT| | |].
      * intros captured MEMBER.
        pose proof(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OLD]REST].
        destruct(Nat.eq_dec(gateway_held_ticket captured)ticket)as[SAME|DIFFERENT].
        -- rewrite SAME in OLD.
           destruct(gateway_reference_owned_ticket_unique _ _ _ _ _ _ FORMED OWNED OLD)as[PLACE POINTER].
           rewrite POINTER;exists to;rewrite SAME;exact CAPTURED.
        -- exists place;apply RETAINED;assumption.
      * unfold GatewayObjects.gateway_objects_frame;intros;assumption.
      * unfold GatewayObjects.gateway_object_privacy_frame;intros;assumption.
    + split;assumption.
Qed.

Theorem gateway_reference_return_source_owner {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function expression source continuation environment temporaries pointer before world after ledger ticket:
  gateway_reference_temporary_expression expression=Some source->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth continuation)source)ticket pointer->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth continuation))
    (gateway_reference_entries ledger)=None->
  gateway_step backend ge
    (gateway_live(State function(Sreturn(Some expression))continuation environment temporaries before)world)
    (gateway_source E0)(gateway_live(Returnstate pointer(call_cont continuation)after)world)->
  exists next,
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(State function(Sreturn(Some expression))continuation environment temporaries before)world)
      (gateway_reference_valid ledger)[gateway_source E0]
      (gateway_live(Returnstate pointer(call_cont continuation)after)world)(gateway_reference_valid next) /\
    gateway_reference_ledger_well_formed next /\
    gateway_reference_owns next(gateway_reference_result(gateway_reference_depth continuation))ticket pointer /\
    gateway_reference_place_value ge(Returnstate pointer(call_cont continuation)after)
      (gateway_reference_result(gateway_reference_depth continuation))pointer /\
    (forall value,gateway_reference_count next value=gateway_reference_count ledger value).
Proof.
  intros FORM FORMED OWNED VACANT SOURCE.
  destruct(gateway_reference_move_selected ledger(gateway_reference_temporary(gateway_reference_depth continuation)source)
    (gateway_reference_result(gateway_reference_depth continuation))ticket pointer FORMED OWNED)
    as[next[MOVE[WELL[CAPTURED[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    exact(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER OWNER).
  - assert(SELECT:@gateway_reference_frame_select World Event
      (gateway_live(State function(Sreturn(Some expression))continuation environment temporaries before)world)
      (gateway_source E0)(gateway_live(Returnstate pointer(call_cont continuation)after)world)
      (gateway_reference_valid ledger)=gateway_reference_move
        (gateway_reference_temporary(gateway_reference_depth continuation)source)
        (gateway_reference_result(gateway_reference_depth continuation))).
    { destruct expression;cbn[gateway_reference_temporary_expression]in FORM;try discriminate.
      - inversion FORM;subst;reflexivity.
      - match goal with nested:Clight.expr|-_=>destruct nested;
          cbn[gateway_reference_temporary_expression]in FORM;try discriminate end.
        inversion FORM;subst;reflexivity. }
    exists next;split.
    + econstructor;[exact SOURCE|]. rewrite SELECT,MOVE;constructor.
    + split;[exact WELL|]. split;[exact CAPTURED|]. split;[|exact COUNTS].
      rewrite<-gateway_reference_call_cont_depth;apply gateway_reference_result_binding.
Qed.
