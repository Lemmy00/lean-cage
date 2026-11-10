(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: One selected reference release retains independent aliased owners. *)
From Stdlib Require Import List Lia Sorting.Permutation.
From compcert Require Import Values.
From HostGateway Require Import GatewayMachine GatewayReferenceLedger GatewayPython GatewayObjects GatewayReferences.
Import ListNotations.

Definition gateway_reference_counts_fit ledger python :Prop:=
  forall pointer,(gateway_reference_count ledger pointer<=python_native_strong python pointer)%nat.

Lemma gateway_reference_take_counts owner entries selected remaining pointer:
  gateway_reference_take owner entries=Some(selected,remaining)->
  count_occ Val.eq(map gateway_reference_pointer entries)pointer=
    (if Val.eq(gateway_reference_pointer selected)pointer then
      S(count_occ Val.eq(map gateway_reference_pointer remaining)pointer)
     else count_occ Val.eq(map gateway_reference_pointer remaining)pointer).
Proof.
  intro TAKE;pose proof(gateway_reference_take_permutation _ _ _ _ TAKE)as PERM.
  apply(Permutation_map gateway_reference_pointer)in PERM.
  apply(proj1(Permutation_count_occ Val.eq _ _))with(x:=pointer)in PERM.
  exact PERM.
Qed.

Lemma gateway_reference_owned_count_positive ledger owner ticket pointer:
  gateway_reference_owns ledger owner ticket pointer->(0<gateway_reference_count ledger pointer)%nat.
Proof.
  intro OWNED;unfold gateway_reference_count;apply count_occ_In.
  apply in_map_iff;exists {|gateway_reference_ticket:=ticket;gateway_reference_owner:=owner;
    gateway_reference_pointer:=pointer|};split;[reflexivity|exact OWNED].
Qed.

Lemma gateway_reference_owned_rooted ledger python heap owner ticket pointer:
  gateway_reference_counts_fit ledger python->gateway_reference_owns ledger owner ticket pointer->
  gateway_rooted python heap pointer.
Proof.
  intros FIT OWNED;apply gateway_direct_root.
  pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(FIT pointer);lia.
Qed.

Theorem gateway_reference_mint_selected ledger owner pointer:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  exists next,
    gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\gateway_reference_ledger_well_formed next /\
    gateway_reference_owns next owner(gateway_reference_next ledger)pointer /\
    (forall place ticket value,gateway_reference_owns ledger place ticket value->
      gateway_reference_owns next place ticket value) /\
    (forall value,gateway_reference_count next value=
      if Val.eq pointer value then S(gateway_reference_count ledger value)
      else gateway_reference_count ledger value).
Proof.
  intros FORMED VACANT.
  set(next:={|gateway_reference_next:=S(gateway_reference_next ledger);
    gateway_reference_entries:=
      {|gateway_reference_ticket:=gateway_reference_next ledger;gateway_reference_owner:=owner;
        gateway_reference_pointer:=pointer|}::gateway_reference_entries ledger|}).
  assert(APPLY:gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
    gateway_reference_valid next)by(cbn;rewrite VACANT;reflexivity).
  exists next;split;[exact APPLY|]. split.
  - eapply gateway_reference_apply_well_formed;eassumption.
  - split;[left;reflexivity|]. split;[intros;right;assumption|].
    intro value;unfold gateway_reference_count;reflexivity.
Qed.

Theorem gateway_reference_mint_counts ledger owner pointer python next_python:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger python->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  python_native_strong next_python pointer=S(python_native_strong python pointer)->
  (forall other,other<>pointer->python_native_strong next_python other=python_native_strong python other)->
  exists next,
    gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\
    gateway_reference_ledger_well_formed next /\gateway_reference_counts_fit next next_python /\
    gateway_reference_owns next owner(gateway_reference_next ledger)pointer /\
    (forall place ticket value,gateway_reference_owns ledger place ticket value->
      gateway_reference_owns next place ticket value).
Proof.
  intros FORMED FIT VACANT CREDIT FRAME.
  destruct(gateway_reference_mint_selected ledger owner pointer FORMED VACANT)
    as[next[APPLY[WELL[OWNED[RETAINED COUNTS]]]]].
  exists next;split;[exact APPLY|]. split;[exact WELL|]. split.
  - intro value;specialize(FIT value);rewrite(COUNTS value).
    destruct(Val.eq pointer value)as[SAME|DIFFERENT].
    + subst value;lia.
    + rewrite(FRAME value ltac:(congruence));exact FIT.
  - split;assumption.
Qed.

Theorem gateway_reference_move_selected ledger from to ticket pointer:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger from ticket pointer->
  (forall entry,In entry(gateway_reference_entries ledger)->gateway_reference_owner entry=to->
    gateway_reference_ticket entry=ticket)->
  exists next,
    gateway_reference_apply(gateway_reference_move from to)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\gateway_reference_ledger_well_formed next /\
    gateway_reference_owns next to ticket pointer /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
      gateway_reference_owns next place other value) /\
    (forall value,gateway_reference_count next value=gateway_reference_count ledger value).
Proof.
  intros FORMED OWNED VACANT.
  destruct(gateway_reference_take_owned _ _ _ _ FORMED OWNED)as[remaining TAKE].
  destruct FORMED as[TICKETS[OWNERS BOUNDS]].
  destruct(gateway_reference_take_nodup gateway_reference_ticket _ _ _ _ TAKE TICKETS)as[_ ABSENT].
  destruct(gateway_reference_take_members _ _ _ _ TAKE)as[SELECTED SUBSET].
  assert(FREE:gateway_reference_take to remaining=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;apply ABSENT.
    assert(SAME:gateway_reference_ticket entry=ticket)by(apply VACANT;[apply SUBSET;exact MEMBER|exact OWNER]).
    apply in_map_iff;exists entry;split;[exact SAME|exact MEMBER]. }
  set(next:={|gateway_reference_next:=gateway_reference_next ledger;
    gateway_reference_entries:=
      {|gateway_reference_ticket:=ticket;gateway_reference_owner:=to;gateway_reference_pointer:=pointer|}::remaining|}).
  assert(APPLY:gateway_reference_apply(gateway_reference_move from to)(gateway_reference_valid ledger)=
    gateway_reference_valid next)by(cbn;rewrite TAKE,FREE;reflexivity).
  exists next;split;[exact APPLY|]. split.
  - exact(gateway_reference_apply_well_formed(gateway_reference_move from to)ledger next
      (conj TICKETS(conj OWNERS BOUNDS))APPLY).
  - split;[left;reflexivity|]. split.
    + intros place other value DIFFERENT OLD.
      pose proof(gateway_reference_take_permutation _ _ _ _ TAKE)as PERM.
      apply(Permutation_in _ PERM)in OLD;destruct OLD as[SAME|REST];[|right;exact REST].
      exfalso;apply DIFFERENT;congruence.
    + intro value;unfold gateway_reference_count;cbn.
      symmetry;exact(gateway_reference_take_counts _ _ _ _ _ TAKE).
Qed.

Lemma gateway_reference_move_keeps_vacant ledger from to other next:
  gateway_reference_take other(gateway_reference_entries ledger)=None->other<>to->
  gateway_reference_apply(gateway_reference_move from to)(gateway_reference_valid ledger)=
    gateway_reference_valid next->
  gateway_reference_take other(gateway_reference_entries next)=None.
Proof.
  intros VACANT DIFFERENT;unfold gateway_reference_apply.
  destruct(gateway_reference_take from(gateway_reference_entries ledger))as[[selected remaining]|]eqn:TAKE;
    [|discriminate].
  destruct(gateway_reference_take to remaining)as[[occupied tail]|]eqn:FREE;[discriminate|].
  intro SAME;injection SAME as SAME;subst next.
  change(gateway_reference_take other
    ({|gateway_reference_ticket:=gateway_reference_ticket selected;gateway_reference_owner:=to;
       gateway_reference_pointer:=gateway_reference_pointer selected|}::remaining)=None).
  apply gateway_reference_take_none;intros entry[HEAD|REST]OWNER.
  - subst entry;cbn in OWNER;congruence.
  - apply(proj1(gateway_reference_take_none _ _)VACANT entry);[|exact OWNER].
    apply(proj2(gateway_reference_take_members _ _ _ _ TAKE));exact REST.
Qed.

Theorem gateway_reference_release_selected ledger owner ticket pointer:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger owner ticket pointer->
  exists next,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\
    gateway_reference_ledger_well_formed next /\
    (forall place value,~gateway_reference_owns next place ticket value) /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
      gateway_reference_owns next place other value) /\
    (forall value,gateway_reference_count ledger value=
      if Val.eq pointer value then S(gateway_reference_count next value)
      else gateway_reference_count next value).
Proof.
  intros FORMED OWNED;destruct(gateway_reference_take_owned _ _ _ _ FORMED OWNED)as[remaining TAKE].
  set(selected:={|gateway_reference_ticket:=ticket;gateway_reference_owner:=owner;
    gateway_reference_pointer:=pointer|}).
  set(next:={|gateway_reference_next:=gateway_reference_next ledger;gateway_reference_entries:=remaining|}).
  assert(APPLY:gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=
    gateway_reference_valid next).
  { cbn;rewrite TAKE;cbn;destruct(Val.eq pointer pointer);[reflexivity|contradiction]. }
  exists next;split;[exact APPLY|]. split.
  - eapply gateway_reference_apply_well_formed;eassumption.
  - destruct FORMED as[TICKETS[OWNERS BOUNDS]].
    destruct(gateway_reference_take_nodup gateway_reference_ticket _ _ _ _ TAKE TICKETS)as[_ ABSENT].
    split.
    + intros place value BAD;apply ABSENT;apply in_map_iff.
      exists {|gateway_reference_ticket:=ticket;gateway_reference_owner:=place;
        gateway_reference_pointer:=value|};split;[reflexivity|exact BAD].
    + split.
      * intros place other value DIFFERENT OLD.
        pose proof(gateway_reference_take_permutation _ _ _ _ TAKE)as PERM.
        apply(Permutation_in _ PERM)in OLD;destruct OLD as[SAME|REST];[|exact REST].
        exfalso;apply DIFFERENT;congruence.
      * intro value;unfold gateway_reference_count;cbn.
        exact(gateway_reference_take_counts _ _ _ _ _ TAKE).
Qed.

Theorem gateway_reference_release_counts ledger owner ticket pointer python next_python:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger python->
  gateway_reference_owns ledger owner ticket pointer->
  python_native_strong python pointer=S(python_native_strong next_python pointer)->
  (forall other,other<>pointer->python_native_strong next_python other=python_native_strong python other)->
  exists next,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\
    gateway_reference_ledger_well_formed next /\gateway_reference_counts_fit next next_python /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
      gateway_reference_owns next place other value).
Proof.
  intros FORMED FIT OWNED DEBIT FRAME.
  destruct(gateway_reference_release_selected _ _ _ _ FORMED OWNED)
    as[next[APPLY[NEXT_FORMED[REMOVED[RETAINED COUNTS]]]]].
  exists next;split;[exact APPLY|]. split;[exact NEXT_FORMED|]. split;[|exact RETAINED].
  intro value;specialize(FIT value);specialize(COUNTS value).
  destruct(Val.eq pointer value)as[SAME|DIFFERENT].
  - subst value;lia.
  - rewrite(FRAME value ltac:(congruence));lia.
Qed.

Theorem gateway_reference_actual_decref {World Event}(backend:gateway_backend World Event)
    python objects(references:gateway_reference_runtime backend python objects)
    ledger owner ticket pointer before world result after next_world observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger owner ticket pointer->
  gateway_objects_ready(python world)(objects world)before->gateway_destructible(objects world)pointer->
  gateway_object_operation backend gateway_api_decref[pointer]before world result after next_world observed->
  exists next,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\
    gateway_reference_ledger_well_formed next /\gateway_reference_counts_fit next(python next_world) /\
    gateway_reference_return(python world)(objects world)before pointer(python next_world)(objects next_world)after /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
      gateway_reference_owns next place other value).
Proof.
  intros FORMED FIT OWNED READY DESTRUCTIBLE OPERATION.
  assert(POSITIVE:(0<python_native_strong(python world)pointer)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(FIT pointer);lia. }
  pose proof(gateway_runtime_decref_objects _ _ _ references _ _ _ _ _ _ _ READY POSITIVE DESTRUCTIBLE OPERATION)
    as RETURN.
  destruct(gateway_reference_release_counts ledger owner ticket pointer(python world)(python next_world)
    FORMED FIT OWNED(gateway_reference_owned _ _ _ _ _ _ _ RETURN))as[next[APPLY[WELL[COUNTS RETAINED]]]].
  - intros other DIFFERENT;apply(gateway_reference_others _ _ _ _ _ _ _ RETURN).
    intros[HEAD|TAIL];[congruence|contradiction].
  - exists next;exact(conj APPLY(conj WELL(conj COUNTS(conj RETURN RETAINED)))).
Qed.
