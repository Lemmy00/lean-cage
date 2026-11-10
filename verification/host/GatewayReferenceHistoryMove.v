(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Ordinary source moves preserve the unreleased-reference archive. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values.
From HostGateway Require Import GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHistory
  GatewayReferenceAbandon.
Import ListNotations.

Theorem gateway_history_move_owned position ledger retired from to ticket pointer:
  gateway_history_well_formed position ledger retired->gateway_reference_owns ledger from ticket pointer->
  gateway_reference_take to(gateway_reference_entries ledger)=None->
  exists next,
    gateway_history_apply position(gateway_history_current(gateway_reference_move from to))
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}=
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=retired|} /\
    gateway_history_well_formed(S position)next retired /\gateway_reference_owns next to ticket pointer /\
    (forall value,gateway_history_total_count next retired value=gateway_history_total_count ledger retired value) /\
    (forall old_place old_ticket value,old_ticket<>ticket->gateway_reference_owns ledger old_place old_ticket value->
      gateway_reference_owns next old_place old_ticket value).
Proof.
  intros FORMED OWNED VACANT;pose proof(gateway_history_current_formed _ _ _ FORMED)as ACTIVE.
  destruct(gateway_reference_take_owned _ _ _ _ ACTIVE OWNED)as[remaining TAKE].
  set(selected:={|gateway_reference_ticket:=ticket;gateway_reference_owner:=from;gateway_reference_pointer:=pointer|}).
  set(moved:={|gateway_reference_ticket:=ticket;gateway_reference_owner:=to;gateway_reference_pointer:=pointer|}).
  pose proof(gateway_history_drop_active _ _ _ _ _ _ FORMED TAKE)as DROPPED.
  destruct ACTIVE as[TICKETS[OWNERS BOUNDS]].
  destruct(gateway_reference_take_nodup gateway_reference_ticket _ _ _ _ TAKE TICKETS)as[REST_TICKETS FRESH].
  destruct(gateway_reference_take_members _ _ _ _ TAKE)as[SELECTED SUBSET].
  assert(DESTINATION:gateway_reference_take to remaining=None).
  { apply gateway_reference_take_none;intros entry MEMBER SAME.
    apply(proj1(gateway_reference_take_none _ _)VACANT entry);[apply SUBSET;exact MEMBER|exact SAME]. }
  set(next:=gateway_reference_without ledger(moved::remaining)).
  assert(WELL:gateway_history_well_formed(S position)next retired).
  { eapply(gateway_history_restore_owner(S position)(gateway_reference_without ledger remaining)retired moved).
    - eapply(gateway_history_well_formed_advance position(S position)
        (gateway_reference_without ledger remaining)retired);[lia|exact DROPPED].
    - apply Forall_forall with(x:=selected)in BOUNDS;[exact BOUNDS|exact SELECTED].
    - exact FRESH.
    - intro BAD;apply in_map_iff in BAD;destruct BAD as[entry[SAME MEMBER]].
      apply(proj1(gateway_reference_take_none _ _)DESTINATION entry MEMBER);exact SAME.
    - intros old MEMBER;exact(gateway_history_pool_separate _ _ _ FORMED old MEMBER selected SELECTED). }
  exists next;split.
  - unfold gateway_history_apply,gateway_reference_apply;cbn;rewrite TAKE;cbn;rewrite DESTINATION;reflexivity.
  - split;[exact WELL|]. split;[left;reflexivity|]. split.
    + intro value;unfold gateway_history_total_count,gateway_reference_count;cbn.
      rewrite(gateway_reference_take_counts _ _ _ _ _ TAKE);reflexivity.
    + intros old_place old_ticket value DIFFERENT OLD.
      pose proof(gateway_reference_take_permutation _ _ _ _ TAKE)as PERM.
      apply(Permutation.Permutation_in _ PERM)in OLD;destruct OLD as[SAME|OLD];[exfalso;apply DIFFERENT;congruence|].
      right;exact OLD.
Qed.

Lemma gateway_history_keep_formed position ledger retired:
  gateway_history_well_formed position ledger retired->gateway_history_well_formed(S position)ledger retired.
Proof. intro FORMED;eapply(gateway_history_well_formed_advance position(S position)ledger retired);[lia|exact FORMED]. Qed.
