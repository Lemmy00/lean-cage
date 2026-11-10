(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Retrying initialization accounts for actual owning-global overwrites. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values.
From HostGateway Require Import GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHistory
  GatewayReferenceAbandon.
Import ListNotations.

Theorem gateway_history_clear_owned position ledger retired owner:
  gateway_history_well_formed position ledger retired->
  exists next archived,
    gateway_history_apply position(gateway_history_clear owner)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}=
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|} /\
    gateway_history_well_formed(S position)next archived /\
    gateway_reference_take owner(gateway_reference_entries next)=None /\
    (forall pointer,gateway_history_total_count next archived pointer=gateway_history_total_count ledger retired pointer).
Proof.
  intro FORMED;destruct(gateway_reference_take owner(gateway_reference_entries ledger))as[[old remaining]|]eqn:TAKE.
  - exists(gateway_reference_without ledger remaining),
      ({|gateway_abandoned_source_position:=position;gateway_abandoned_owner:=old|}::retired).
    split;[cbn;rewrite TAKE;reflexivity|]. split.
    + eapply gateway_history_abandon_active;eassumption.
    + split.
      * pose proof(gateway_history_current_formed _ _ _ FORMED)as[_[OWNERS BOUNDS]].
        destruct(gateway_reference_take_nodup gateway_reference_owner _ _ _ _ TAKE OWNERS)as[_ ABSENT].
        destruct(gateway_reference_take_decomposition _ _ _ _ TAKE)as(prefix&suffix&ENTRIES&REMAINING&OWNER).
        apply gateway_reference_take_none;intros entry MEMBER SAME;apply ABSENT;rewrite OWNER,<-SAME.
        apply in_map;exact MEMBER.
      * intro pointer;eapply gateway_history_abandon_count;exact TAKE.
  - exists ledger,retired;split;[cbn;rewrite TAKE;reflexivity|]. split.
    + eapply(gateway_history_well_formed_advance position(S position)ledger retired);[lia|exact FORMED].
    + split;[exact TAKE|reflexivity].
Qed.

Theorem gateway_history_assign_owned position ledger retired from to ticket pointer:
  gateway_history_well_formed position ledger retired->gateway_reference_owns ledger from ticket pointer->
  exists next archived,
    gateway_history_apply position(gateway_history_assign from to)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}=
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|} /\
    gateway_history_well_formed(S position)next archived /\gateway_reference_owns next to ticket pointer /\
    (forall value,gateway_history_total_count next archived value=gateway_history_total_count ledger retired value) /\
    (forall old_place old_ticket value,old_ticket<>ticket->old_place<>to->
      gateway_reference_owns ledger old_place old_ticket value->gateway_reference_owns next old_place old_ticket value).
Proof.
  intros FORMED OWNED;pose proof(gateway_history_current_formed _ _ _ FORMED)as ACTIVE.
  destruct(gateway_reference_take_owned _ _ _ _ ACTIVE OWNED)as[remaining TAKE].
  set(selected:={|gateway_reference_ticket:=ticket;gateway_reference_owner:=from;gateway_reference_pointer:=pointer|}).
  set(moved:={|gateway_reference_ticket:=ticket;gateway_reference_owner:=to;gateway_reference_pointer:=pointer|}).
  pose proof(gateway_history_drop_active _ _ _ _ _ _ FORMED TAKE)as DROPPED.
  destruct ACTIVE as[TICKETS[OWNERS BOUNDS]].
  destruct(gateway_reference_take_nodup gateway_reference_ticket _ _ _ _ TAKE TICKETS)as[REST_TICKETS TICKET_FRESH].
  destruct(gateway_reference_take_members _ _ _ _ TAKE)as[SELECTED REST_SUBSET].
  assert(BOUND:(ticket<gateway_reference_next ledger)%nat).
  { apply Forall_forall with(x:=selected)in BOUNDS;[exact BOUNDS|exact SELECTED]. }
  destruct(gateway_reference_take to remaining)as[[old rest]|]eqn:DESTINATION.
  - set(archived:={|gateway_abandoned_source_position:=position;gateway_abandoned_owner:=old|}::retired).
    set(next:=gateway_reference_without ledger(moved::rest)).
    assert(RETIRED:gateway_history_well_formed(S position)(gateway_reference_without ledger rest)archived).
    { eapply(gateway_history_abandon_active position(gateway_reference_without ledger remaining)retired to old rest);
        [exact DROPPED|exact DESTINATION]. }
    destruct(gateway_reference_take_members _ _ _ _ DESTINATION)as[OLD_IN REST_SUBSET_2].
    pose proof(gateway_history_current_formed _ _ _ DROPPED)as[_[REST_OWNERS _]].
    destruct(gateway_reference_take_nodup gateway_reference_owner _ _ _ _ DESTINATION REST_OWNERS)as[_ OWNER_FRESH].
    destruct(gateway_reference_take_decomposition _ _ _ _ DESTINATION)
      as(prefix&suffix&ENTRIES&REST&OLD_OWNER).
    assert(NEXT_FORMED:gateway_history_well_formed(S position)next archived).
    { eapply(gateway_history_restore_owner(S position)(gateway_reference_without ledger rest)archived moved).
      - exact RETIRED.
      - exact BOUND.
      - intro BAD;apply in_map_iff in BAD;destruct BAD as[entry[SAME MEMBER]].
        apply TICKET_FRESH;apply in_map_iff;exists entry;split;[exact SAME|apply REST_SUBSET_2;exact MEMBER].
      - cbn;rewrite<-OLD_OWNER;exact OWNER_FRESH.
      - intros earlier[NEW|MEMBER].
        + subst earlier;cbn;intro SAME;apply TICKET_FRESH;apply in_map_iff;exists old;split;[symmetry;exact SAME|exact OLD_IN].
        + apply(gateway_history_pool_separate _ _ _ FORMED earlier MEMBER selected SELECTED). }
    exists next,archived;split;[cbn;rewrite TAKE;cbn;rewrite DESTINATION;reflexivity|].
    split;[exact NEXT_FORMED|]. split;[left;reflexivity|]. split.
    + intro value;unfold gateway_history_total_count,gateway_reference_count,gateway_abandoned_count;cbn.
      rewrite(gateway_reference_take_counts _ _ _ _ _ TAKE).
      rewrite(gateway_reference_take_counts _ _ _ _ _ DESTINATION).
      cbv beta iota zeta delta[gateway_reference_pointer gateway_abandoned_pointer gateway_abandoned_owner].
      repeat match goal with|-context[Val.eq ?first ?second]=>destruct(Val.eq first second)end;lia.
    + intros old_place old_ticket value DIFFERENT OTHER OLD.
      pose proof(gateway_reference_take_permutation _ _ _ _ TAKE)as FIRST_PERM.
      apply(Permutation.Permutation_in _ FIRST_PERM)in OLD;destruct OLD as[SAME|OLD];[exfalso;apply DIFFERENT;congruence|].
      pose proof(gateway_reference_take_permutation _ _ _ _ DESTINATION)as SECOND_PERM.
      apply(Permutation.Permutation_in _ SECOND_PERM)in OLD;destruct OLD as[SAME|OLD];[|right;exact OLD].
      exfalso;apply OTHER;rewrite<-OLD_OWNER;rewrite SAME;reflexivity.
  - set(next:=gateway_reference_without ledger(moved::remaining)).
    assert(NEXT_FORMED:gateway_history_well_formed(S position)next retired).
    { eapply(gateway_history_restore_owner(S position)(gateway_reference_without ledger remaining)retired moved).
      - eapply(gateway_history_well_formed_advance position(S position)
          (gateway_reference_without ledger remaining)retired);[lia|exact DROPPED].
      - exact BOUND.
      - exact TICKET_FRESH.
      - intro BAD;apply in_map_iff in BAD;destruct BAD as[entry[SAME MEMBER]].
        apply(proj1(gateway_reference_take_none to remaining)DESTINATION entry MEMBER);exact SAME.
      - intros old MEMBER;apply(gateway_history_pool_separate _ _ _ FORMED old MEMBER selected SELECTED). }
    exists next,retired;split;[cbn;rewrite TAKE;cbn;rewrite DESTINATION;reflexivity|].
    split;[exact NEXT_FORMED|]. split;[left;reflexivity|]. split.
    + intro value;unfold gateway_history_total_count,gateway_reference_count;cbn.
      rewrite(gateway_reference_take_counts _ _ _ _ _ TAKE);reflexivity.
    + intros old_place old_ticket value DIFFERENT OTHER OLD.
      pose proof(gateway_reference_take_permutation _ _ _ _ TAKE)as FIRST_PERM.
      apply(Permutation.Permutation_in _ FIRST_PERM)in OLD;destruct OLD as[SAME|OLD];[exfalso;apply DIFFERENT;congruence|].
      right;exact OLD.
Qed.
