(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Lost C-global owners stay accounted without granting active authority. *)
From Stdlib Require Import List Lia PeanoNat.
From compcert Require Import Values.
From HostGateway Require Import GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHistory GatewayPython.
Import ListNotations.

Definition gateway_abandoned_ticket(entry:gateway_abandoned_reference):nat:=
  gateway_reference_ticket(gateway_abandoned_owner entry).
Definition gateway_abandoned_pointer(entry:gateway_abandoned_reference):Values.val:=
  gateway_reference_pointer(gateway_abandoned_owner entry).
Definition gateway_abandoned_count retired pointer:nat:=count_occ Val.eq(map gateway_abandoned_pointer retired)pointer.
Definition gateway_history_total_count ledger retired pointer:nat:=
  gateway_reference_count ledger pointer+gateway_abandoned_count retired pointer.
Definition gateway_history_counts_fit ledger retired python:Prop:=
  forall pointer,(gateway_history_total_count ledger retired pointer<=python_native_strong python pointer)%nat.

Record gateway_history_well_formed position ledger retired:Prop:={
  gateway_history_current_formed:gateway_reference_ledger_well_formed ledger;
  gateway_history_retired_unique:NoDup(map gateway_abandoned_ticket retired);
  gateway_history_retired_bound:Forall(fun old=>(gateway_abandoned_ticket old<gateway_reference_next ledger)%nat)retired;
  gateway_history_pool_separate:forall old,In old retired->forall entry,In entry(gateway_reference_entries ledger)->
    gateway_reference_ticket entry<>gateway_abandoned_ticket old;
  gateway_history_retired_prior:Forall(fun old=>(gateway_abandoned_source_position old<position)%nat)retired
}.

Definition gateway_reference_without ledger entries:gateway_reference_ledger:={|
  gateway_reference_next:=gateway_reference_next ledger;gateway_reference_entries:=entries|}.

Lemma gateway_history_well_formed_advance position next ledger retired:
  (position<=next)%nat->gateway_history_well_formed position ledger retired->
  gateway_history_well_formed next ledger retired.
Proof.
  intros LE FORMED;destruct FORMED as[ACTIVE UNIQUE BOUND SEPARATE PRIOR];constructor;try assumption.
  apply Forall_forall;intros old MEMBER;apply Forall_forall with(x:=old)in PRIOR;[lia|exact MEMBER].
Qed.

Lemma gateway_history_drop_active position ledger retired owner selected remaining:
  gateway_history_well_formed position ledger retired->
  gateway_reference_take owner(gateway_reference_entries ledger)=Some(selected,remaining)->
  gateway_history_well_formed position(gateway_reference_without ledger remaining)retired.
Proof.
  intros FORMED TAKE;destruct FORMED as[ACTIVE UNIQUE BOUND SEPARATE PRIOR].
  assert(APPLY:gateway_reference_apply(gateway_reference_release owner(gateway_reference_pointer selected))
    (gateway_reference_valid ledger)=gateway_reference_valid(gateway_reference_without ledger remaining)).
  { cbn;rewrite TAKE;destruct(Val.eq(gateway_reference_pointer selected)(gateway_reference_pointer selected));
      [reflexivity|contradiction]. }
  constructor;try assumption.
  - eapply gateway_reference_apply_well_formed;[exact ACTIVE|exact APPLY].
  - intros old MEMBER entry IN;apply SEPARATE;[exact MEMBER|].
    apply(proj2(gateway_reference_take_members _ _ _ _ TAKE));exact IN.
Qed.

Theorem gateway_history_abandon_active position ledger retired owner selected remaining:
  gateway_history_well_formed position ledger retired->
  gateway_reference_take owner(gateway_reference_entries ledger)=Some(selected,remaining)->
  gateway_history_well_formed(S position)(gateway_reference_without ledger remaining)
    ({|gateway_abandoned_source_position:=position;gateway_abandoned_owner:=selected|}::retired).
Proof.
  intros FORMED TAKE;pose proof FORMED as[ACTIVE UNIQUE BOUND SEPARATE PRIOR].
  pose proof(gateway_history_drop_active _ _ _ _ _ _ FORMED TAKE)as[DROPPED _ _ REST_SEPARATE _].
  destruct(gateway_reference_take_members _ _ _ _ TAKE)as[SELECTED SUBSET].
  destruct ACTIVE as[TICKETS[OWNERS ACTIVE_BOUND]].
  destruct(gateway_reference_take_nodup gateway_reference_ticket _ _ _ _ TAKE TICKETS)as[_ REST_FRESH].
  constructor;cbn.
  - exact DROPPED.
  - constructor;[|exact UNIQUE]. intro BAD;apply in_map_iff in BAD.
    destruct BAD as[old[SAME MEMBER]].
    apply(SEPARATE old MEMBER selected SELECTED);exact(eq_sym SAME).
  - constructor.
    + apply Forall_forall with(x:=selected)in ACTIVE_BOUND;assumption.
    + exact BOUND.
  - intros old[NEW|MEMBER]entry IN.
    + subst old;cbn;intro SAME;apply REST_FRESH;apply in_map_iff;exists entry;split;
        [exact SAME|exact IN].
    + apply REST_SEPARATE;assumption.
  - constructor;[cbn;lia|]. apply Forall_forall;intros old MEMBER.
    apply Forall_forall with(x:=old)in PRIOR;[lia|exact MEMBER].
Qed.

Theorem gateway_history_abandon_count ledger retired owner selected remaining position pointer:
  gateway_reference_take owner(gateway_reference_entries ledger)=Some(selected,remaining)->
  gateway_history_total_count(gateway_reference_without ledger remaining)
    ({|gateway_abandoned_source_position:=position;gateway_abandoned_owner:=selected|}::retired)pointer=
  gateway_history_total_count ledger retired pointer.
Proof.
  intro TAKE;unfold gateway_history_total_count,gateway_reference_count,gateway_abandoned_count;cbn.
  rewrite(gateway_reference_take_counts _ _ _ _ _ TAKE).
  unfold gateway_abandoned_pointer;cbn.
  destruct(Val.eq(gateway_reference_pointer selected)pointer);lia.
Qed.

Theorem gateway_history_retired_not_active position ledger retired old place pointer:
  gateway_history_well_formed position ledger retired->In old retired->
  ~gateway_reference_owns ledger place(gateway_abandoned_ticket old)pointer.
Proof.
  intros FORMED MEMBER OWNED.
  apply(gateway_history_pool_separate _ _ _ FORMED old MEMBER
    {|gateway_reference_ticket:=gateway_abandoned_ticket old;gateway_reference_owner:=place;
      gateway_reference_pointer:=pointer|}OWNED);reflexivity.
Qed.

Lemma gateway_history_restore_owner position ledger retired entry:
  gateway_history_well_formed position ledger retired->
  (gateway_reference_ticket entry<gateway_reference_next ledger)%nat->
  ~In(gateway_reference_ticket entry)(map gateway_reference_ticket(gateway_reference_entries ledger))->
  ~In(gateway_reference_owner entry)(map gateway_reference_owner(gateway_reference_entries ledger))->
  (forall old,In old retired->gateway_reference_ticket entry<>gateway_abandoned_ticket old)->
  gateway_history_well_formed position
    (gateway_reference_without ledger(entry::gateway_reference_entries ledger))retired.
Proof.
  intros FORMED BOUND TICKET OWNER FRESH;destruct FORMED as[[TICKETS[OWNERS BOUNDS]]UNIQUE RETIRED_BOUND SEPARATE PRIOR].
  constructor;cbn.
  - split;[constructor;assumption|]. split;constructor;assumption.
  - exact UNIQUE.
  - exact RETIRED_BOUND.
  - intros old MEMBER current[HEAD|REST];[subst current;apply FRESH;exact MEMBER|apply SEPARATE;assumption].
  - exact PRIOR.
Qed.
