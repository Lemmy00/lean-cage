(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Owned references are source places, even for pointer aliases. *)
From Stdlib Require Import ZArith List Lia Bool Sorting.Permutation.
From compcert Require Import Coqlib Values Memory.
Import ListNotations.

Inductive gateway_reference_place :=
| gateway_reference_temporary (invocation:nat)(identifier:positive)
| gateway_reference_cell (object:block)(offset:Z)
| gateway_reference_result (invocation:nat)
| gateway_reference_argument (invocation:nat)(index:nat)
| gateway_reference_global (identifier:positive).

Definition gateway_reference_place_eq : forall first second:gateway_reference_place,
    {first=second}+{first<>second}.
Proof. decide equality; auto using PeanoNat.Nat.eq_dec, Pos.eq_dec, Z.eq_dec. Defined.

Record gateway_owned_reference := {
  gateway_reference_ticket : nat;
  gateway_reference_owner : gateway_reference_place;
  gateway_reference_pointer : Values.val
}.

Record gateway_reference_ledger := {
  gateway_reference_next : nat;
  gateway_reference_entries : list gateway_owned_reference
}.

Definition gateway_reference_ledger_well_formed ledger :Prop:=
  NoDup(map gateway_reference_ticket(gateway_reference_entries ledger)) /\
  NoDup(map gateway_reference_owner(gateway_reference_entries ledger)) /\
  Forall(fun entry=>(gateway_reference_ticket entry<gateway_reference_next ledger)%nat)
    (gateway_reference_entries ledger).

Definition gateway_reference_empty := {|gateway_reference_next:=0;gateway_reference_entries:=[]|}.

Fixpoint gateway_reference_take owner entries :option(gateway_owned_reference*list gateway_owned_reference):=
  match entries with
  |[]=>None
  |entry::rest=>
    if gateway_reference_place_eq owner(gateway_reference_owner entry) then Some(entry,rest)
    else match gateway_reference_take owner rest with
      |Some(selected,remaining)=>Some(selected,entry::remaining)
      |None=>None
      end
  end.

Inductive gateway_reference_action :=
| gateway_reference_keep
| gateway_reference_mint (owner:gateway_reference_place)(pointer:Values.val)
| gateway_reference_move (from to:gateway_reference_place)
| gateway_reference_release (owner:gateway_reference_place)(pointer:Values.val)
| gateway_reference_unclassified.

Inductive gateway_reference_error :=
| gateway_reference_occupied
| gateway_reference_missing
| gateway_reference_mismatch
| gateway_reference_unknown.

Inductive gateway_reference_status :=
| gateway_reference_valid (ledger:gateway_reference_ledger)
| gateway_reference_invalid (reason:gateway_reference_error).

Definition gateway_reference_apply action status :gateway_reference_status:=
  match status with
  |gateway_reference_invalid reason=>gateway_reference_invalid reason
  |gateway_reference_valid ledger=>
    let entries:=gateway_reference_entries ledger in
    match action with
    |gateway_reference_keep=>status
    |gateway_reference_unclassified=>gateway_reference_invalid gateway_reference_unknown
    |gateway_reference_mint owner pointer=>
      match gateway_reference_take owner entries with
      |Some _=>gateway_reference_invalid gateway_reference_occupied
      |None=>gateway_reference_valid
        {|gateway_reference_next:=S(gateway_reference_next ledger);
          gateway_reference_entries:=
            {|gateway_reference_ticket:=gateway_reference_next ledger;
              gateway_reference_owner:=owner;gateway_reference_pointer:=pointer|}::entries|}
      end
    |gateway_reference_release owner pointer=>
      match gateway_reference_take owner entries with
      |None=>gateway_reference_invalid gateway_reference_missing
      |Some(selected,remaining)=>
        if Val.eq pointer(gateway_reference_pointer selected) then
          gateway_reference_valid
            {|gateway_reference_next:=gateway_reference_next ledger;gateway_reference_entries:=remaining|}
        else gateway_reference_invalid gateway_reference_mismatch
      end
    |gateway_reference_move from to=>
      match gateway_reference_take from entries with
      |None=>gateway_reference_invalid gateway_reference_missing
      |Some(selected,remaining)=>
        match gateway_reference_take to remaining with
        |Some _=>gateway_reference_invalid gateway_reference_occupied
        |None=>gateway_reference_valid
          {|gateway_reference_next:=gateway_reference_next ledger;
            gateway_reference_entries:=
              {|gateway_reference_ticket:=gateway_reference_ticket selected;
                gateway_reference_owner:=to;gateway_reference_pointer:=gateway_reference_pointer selected|}
                ::remaining|}
        end
      end
    end
  end.

Definition gateway_reference_owns ledger owner ticket pointer :Prop:=
  In {|gateway_reference_ticket:=ticket;gateway_reference_owner:=owner;
        gateway_reference_pointer:=pointer|}(gateway_reference_entries ledger).

Definition gateway_reference_count ledger pointer :nat:=
  count_occ Val.eq(map gateway_reference_pointer(gateway_reference_entries ledger))pointer.

Lemma gateway_reference_take_decomposition owner entries selected remaining :
  gateway_reference_take owner entries=Some(selected,remaining)->
  exists prefix suffix,entries=prefix++selected::suffix /\remaining=prefix++suffix /\
    gateway_reference_owner selected=owner.
Proof.
  revert selected remaining;induction entries as[|entry rest IH];intros selected remaining;cbn;[discriminate|].
  destruct(gateway_reference_place_eq owner(gateway_reference_owner entry))as[SAME|DIFFERENT].
  - intro EQUAL;injection EQUAL as SELECT REST;subst selected remaining;exists[],rest;cbn;auto.
  - destruct(gateway_reference_take owner rest)as[[found tail]|]eqn:TAKE;[|discriminate].
    intro EQUAL;inversion EQUAL;subst found remaining.
    destruct(IH selected tail eq_refl)as(prefix&suffix&ENTRIES&REMAINING&OWNER).
    exists(entry::prefix),suffix;cbn;repeat split;congruence.
Qed.

Lemma gateway_reference_take_none owner entries :
  gateway_reference_take owner entries=None <->
    forall entry,In entry entries->gateway_reference_owner entry<>owner.
Proof.
  induction entries as[|entry rest IH];cbn.
  - split;[intros _ item BAD;contradiction|reflexivity].
  - destruct(gateway_reference_place_eq owner(gateway_reference_owner entry))as[SAME|DIFFERENT].
    + split;[discriminate|intro ABSENT;exfalso;apply(ABSENT entry);auto].
    + destruct(gateway_reference_take owner rest)as[[found tail]|]eqn:TAKE.
      * split;[discriminate|]. intro ABSENT.
        assert(NONE:Some(found,tail)=None).
        { apply IH;intros item MEMBER;apply ABSENT;auto. }
        discriminate.
      * split.
        -- intros _ item[HEAD|MEMBER];[subst item;congruence|].
           apply(proj1 IH eq_refl item MEMBER).
        -- reflexivity.
Qed.

Lemma gateway_reference_take_members owner entries selected remaining :
  gateway_reference_take owner entries=Some(selected,remaining)->
  In selected entries /\(forall entry,In entry remaining->In entry entries).
Proof.
  intro TAKE;destruct(gateway_reference_take_decomposition _ _ _ _ TAKE)
    as(prefix&suffix&ENTRIES&REMAINING&OWNER);subst entries remaining.
  split;[apply in_or_app;right;left;reflexivity|].
  intros item MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[LEFT|RIGHT];
    apply in_or_app;[left;exact LEFT|right;right;exact RIGHT].
Qed.

Lemma gateway_reference_take_nodup {A}(project:gateway_owned_reference->A)owner entries selected remaining :
  gateway_reference_take owner entries=Some(selected,remaining)->NoDup(map project entries)->
  NoDup(map project remaining) /\~In(project selected)(map project remaining).
Proof.
  intros TAKE UNIQUE.
  destruct(gateway_reference_take_decomposition _ _ _ _ TAKE)
    as(prefix&suffix&ENTRIES&REMAINING&OWNER);subst entries remaining.
  repeat rewrite map_app in UNIQUE|-*;cbn in UNIQUE.
  assert(PERM:Permutation(map project prefix++project selected::map project suffix)
      (project selected::(map project prefix++map project suffix))).
  { symmetry;apply Permutation_middle. }
  apply(Permutation_NoDup PERM)in UNIQUE;inversion UNIQUE;auto.
Qed.

Lemma gateway_reference_take_permutation owner entries selected remaining :
  gateway_reference_take owner entries=Some(selected,remaining)->
  Permutation entries(selected::remaining).
Proof.
  intro TAKE;destruct(gateway_reference_take_decomposition _ _ _ _ TAKE)
    as(prefix&suffix&ENTRIES&REMAINING&OWNER);subst entries remaining.
  symmetry;apply Permutation_middle.
Qed.

Lemma gateway_reference_take_owned ledger owner ticket pointer :
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger owner ticket pointer->
  exists remaining,gateway_reference_take owner(gateway_reference_entries ledger)=
    Some({|gateway_reference_ticket:=ticket;gateway_reference_owner:=owner;
      gateway_reference_pointer:=pointer|},remaining).
Proof.
  intros[TICKETS[OWNERS BOUNDS]]OWNED.
  destruct(gateway_reference_take owner(gateway_reference_entries ledger))as[[selected remaining]|]eqn:TAKE.
  - pose proof(gateway_reference_take_permutation _ _ _ _ TAKE)as PERM.
    apply(Permutation_in _ PERM)in OWNED;destruct OWNED as[SAME|REST].
    + subst selected;eauto.
    + destruct(gateway_reference_take_nodup gateway_reference_owner _ _ _ _ TAKE OWNERS)as[_ ABSENT].
      destruct(gateway_reference_take_decomposition _ _ _ _ TAKE)as(prefix&suffix&ENTRIES&REMAINING&OWNER).
      exfalso;apply ABSENT;rewrite OWNER;apply in_map_iff.
      exists {|gateway_reference_ticket:=ticket;gateway_reference_owner:=owner;
        gateway_reference_pointer:=pointer|};split;[reflexivity|exact REST].
  - apply(proj1(gateway_reference_take_none owner(gateway_reference_entries ledger))TAKE
      {|gateway_reference_ticket:=ticket;gateway_reference_owner:=owner;
        gateway_reference_pointer:=pointer|})in OWNED;cbn in OWNED;contradiction.
Qed.

Lemma gateway_reference_empty_well_formed :gateway_reference_ledger_well_formed gateway_reference_empty.
Proof. repeat split;constructor. Qed.

Lemma gateway_reference_apply_invalid action reason :
  gateway_reference_apply action(gateway_reference_invalid reason)=gateway_reference_invalid reason.
Proof. reflexivity. Qed.

Theorem gateway_reference_apply_well_formed action ledger next :
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_apply action(gateway_reference_valid ledger)=gateway_reference_valid next->
  gateway_reference_ledger_well_formed next.
Proof.
  destruct ledger as[fresh entries];intros[TICKETS[OWNERS BOUNDS]];
    destruct action as[|owner pointer|from to|owner pointer|];cbn;try discriminate.
  - intro SAME;inversion SAME;subst;repeat split;assumption.
  - destruct(gateway_reference_take owner entries)as[[selected remaining]|]eqn:TAKE;[discriminate|].
    intro SAME;inversion SAME;subst;cbn;repeat split.
    + constructor;[|exact TICKETS]. intro MEMBER;apply in_map_iff in MEMBER.
      destruct MEMBER as[entry[TICKET IN]].
      apply Forall_forall with(x:=entry)in BOUNDS;[cbn in *;lia|exact IN].
    + constructor;[|exact OWNERS]. intro MEMBER;apply in_map_iff in MEMBER.
      destruct MEMBER as[entry[OWNER IN]].
      apply(proj1(gateway_reference_take_none owner entries)TAKE entry IN);exact OWNER.
    + constructor;[cbn;lia|]. apply Forall_forall;intros entry MEMBER.
      apply Forall_forall with(x:=entry)in BOUNDS;[cbn in *;lia|exact MEMBER].
  - destruct(gateway_reference_take from entries)as[[selected remaining]|]eqn:TAKE;[|discriminate].
    destruct(gateway_reference_take to remaining)as[[occupied rest]|]eqn:ABSENT;[discriminate|].
    intro SAME;inversion SAME;subst;cbn.
    destruct(gateway_reference_take_nodup gateway_reference_ticket _ _ _ _ TAKE TICKETS)as[REST_TICKETS FRESH].
    destruct(gateway_reference_take_nodup gateway_reference_owner _ _ _ _ TAKE OWNERS)as[REST_OWNERS _].
    destruct(gateway_reference_take_members _ _ _ _ TAKE)as[SELECTED SUBSET].
    repeat split.
    + constructor;assumption.
    + constructor;[|exact REST_OWNERS]. intro MEMBER;apply in_map_iff in MEMBER.
      destruct MEMBER as[entry[OWNER IN]].
      apply(proj1(gateway_reference_take_none to remaining)ABSENT entry IN);exact OWNER.
    + constructor.
      * apply Forall_forall with(x:=selected)in BOUNDS;assumption.
      * apply Forall_forall;intros entry MEMBER;apply Forall_forall with(x:=entry)in BOUNDS;
          [exact BOUNDS|apply SUBSET;exact MEMBER].
  - destruct(gateway_reference_take owner entries)as[[selected remaining]|]eqn:TAKE;[|discriminate].
    destruct(Val.eq pointer(gateway_reference_pointer selected));[|discriminate].
    intro SAME;inversion SAME;subst;cbn.
    destruct(gateway_reference_take_nodup gateway_reference_ticket _ _ _ _ TAKE TICKETS)as[REST_TICKETS _].
    destruct(gateway_reference_take_nodup gateway_reference_owner _ _ _ _ TAKE OWNERS)as[REST_OWNERS _].
    destruct(gateway_reference_take_members _ _ _ _ TAKE)as[_ SUBSET].
    repeat split;try assumption.
    apply Forall_forall;intros entry MEMBER;apply Forall_forall with(x:=entry)in BOUNDS;
      [exact BOUNDS|apply SUBSET;exact MEMBER].
Qed.
