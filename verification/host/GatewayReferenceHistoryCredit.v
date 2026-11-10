(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Constructor credits include previously abandoned allocations. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values.
From HostGateway Require Import GatewayPython GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceRuntime
  GatewayReferenceHistory GatewayReferenceAbandon.
Import ListNotations.

Theorem gateway_history_mint_formed position ledger retired owner pointer:
  gateway_history_well_formed position ledger retired->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  exists next,
    gateway_history_apply position(gateway_history_current(gateway_reference_mint owner pointer))
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}=
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=retired|} /\
    gateway_history_well_formed(S position)next retired /\
    gateway_reference_owns next owner(gateway_reference_next ledger)pointer /\
    (forall value,gateway_history_total_count next retired value=
      if Val.eq pointer value then S(gateway_history_total_count ledger retired value)
      else gateway_history_total_count ledger retired value) /\
    (forall place ticket value,gateway_reference_owns ledger place ticket value->
      gateway_reference_owns next place ticket value).
Proof.
  intros FORMED VACANT;pose proof FORMED as[ACTIVE UNIQUE BOUND SEPARATE PRIOR].
  set(entry:={|gateway_reference_ticket:=gateway_reference_next ledger;gateway_reference_owner:=owner;
    gateway_reference_pointer:=pointer|}).
  set(next:={|gateway_reference_next:=S(gateway_reference_next ledger);
    gateway_reference_entries:=entry::gateway_reference_entries ledger|}).
  assert(APPLY:gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid next)by(cbn;rewrite VACANT;reflexivity).
  exists next;split.
  { change({|gateway_history_active:=gateway_reference_apply(gateway_reference_mint owner pointer)
      (gateway_reference_valid ledger);gateway_history_abandoned:=retired|}=
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=retired|}).
    rewrite APPLY;reflexivity. }
  split.
  - constructor;cbn.
    + eapply gateway_reference_apply_well_formed;[exact ACTIVE|exact APPLY].
    + exact UNIQUE.
    + apply Forall_forall;intros old MEMBER;apply Forall_forall with(x:=old)in BOUND;[lia|exact MEMBER].
    + intros old MEMBER active[NEW|IN].
      * subst active;cbn;intro SAME;apply Forall_forall with(x:=old)in BOUND;[cbn in SAME;lia|exact MEMBER].
      * apply SEPARATE;assumption.
    + apply Forall_forall;intros old MEMBER;apply Forall_forall with(x:=old)in PRIOR;[lia|exact MEMBER].
  - split;[left;reflexivity|]. split.
    + intro value;unfold gateway_history_total_count,gateway_reference_count;cbn.
      change((if Val.eq pointer value then
        S(count_occ Val.eq(map gateway_reference_pointer(gateway_reference_entries ledger))value)
        else count_occ Val.eq(map gateway_reference_pointer(gateway_reference_entries ledger))value)+
          gateway_abandoned_count retired value=
        if Val.eq pointer value then
          S(count_occ Val.eq(map gateway_reference_pointer(gateway_reference_entries ledger))value+
            gateway_abandoned_count retired value)
        else count_occ Val.eq(map gateway_reference_pointer(gateway_reference_entries ledger))value+
          gateway_abandoned_count retired value).
      destruct(Val.eq pointer value);reflexivity.
    + intros place ticket value OLD;right;exact OLD.
Qed.

Theorem gateway_history_credit_mints position ledger retired owner pointer before after:
  gateway_history_well_formed position ledger retired->gateway_history_counts_fit ledger retired before->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->gateway_reference_credit before after pointer->
  exists next,
    gateway_history_apply position(gateway_history_current(gateway_reference_mint owner pointer))
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}=
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=retired|} /\
    gateway_history_well_formed(S position)next retired /\gateway_history_counts_fit next retired after /\
    gateway_reference_owns next owner(gateway_reference_next ledger)pointer /\
    (forall place ticket value,gateway_reference_owns ledger place ticket value->
      gateway_reference_owns next place ticket value).
Proof.
  intros FORMED FIT VACANT CREDIT.
  destruct(gateway_history_mint_formed position ledger retired owner pointer FORMED VACANT)
    as[next[APPLY[WELL[OWNED[COUNTS RETAINED]]]]].
  exists next;split;[exact APPLY|]. split;[exact WELL|]. split.
  - intro value;specialize(FIT value);rewrite COUNTS.
    destruct(Val.eq pointer value)as[SAME|DIFFERENT].
    + subst value;rewrite(gateway_reference_credit_target _ _ _ CREDIT);lia.
    + rewrite(gateway_reference_credit_other _ _ _ CREDIT value ltac:(congruence));exact FIT.
  - split;assumption.
Qed.
