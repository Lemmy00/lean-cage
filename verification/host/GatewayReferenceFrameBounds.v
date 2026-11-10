(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Selected source reference moves preserve the real bindings of
   every other owned place, including aliased pointers. *)
From Stdlib Require Import List PeanoNat Lia.
From compcert Require Import Maps AST Values Memory Clight.
From HostGateway Require Import GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceFrames.
Import ListNotations.

Theorem gateway_reference_move_source_bound ge before after ledger final from to ticket pointer:
  gateway_reference_ledger_well_formed ledger->gateway_reference_source_bound ge before ledger->
  gateway_reference_owns ledger from ticket pointer->
  gateway_reference_take to(gateway_reference_entries ledger)=None->
  gateway_reference_apply(gateway_reference_move from to)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_place_value ge after to pointer->
  (forall owner value,owner<>from->owner<>to->gateway_reference_place_value ge before owner value->
    gateway_reference_place_value ge after owner value)->gateway_reference_source_bound ge after final.
Proof.
  intros FORMED BOUND OWNED VACANT MOVE TARGET PRESERVE.
  destruct(gateway_reference_take_owned _ _ _ _ FORMED OWNED)as[remaining TAKE].
  pose proof(gateway_reference_take_members _ _ _ _ TAKE)as[SELECTED SUBSET].
  destruct(gateway_reference_take_nodup gateway_reference_owner _ _ _ _ TAKE(proj1(proj2 FORMED)))as[UNIQUE ABSENT].
  unfold gateway_reference_apply in MOVE;rewrite TAKE in MOVE.
  destruct(gateway_reference_take to remaining)as[[occupied rest]|]eqn:TO;[discriminate|].
  injection MOVE as FINAL;subst final.
  intros entry MEMBER;destruct MEMBER as[SAME|MEMBER].
  - subst entry;exact TARGET.
  - apply PRESERVE;[| |apply BOUND;apply SUBSET;exact MEMBER].
    + intro SAME;apply ABSENT;apply in_map_iff;exists entry;split;[exact SAME|exact MEMBER].
    + intro SAME;apply(proj1(gateway_reference_take_none _ _)VACANT entry(SUBSET entry MEMBER));exact SAME.
Qed.

Lemma gateway_reference_returned_place_frame ge function destination environment temporaries continuation pointer memory owner value:
  owner<>gateway_reference_result(S(gateway_reference_depth continuation))->
  owner<>gateway_reference_temporary(gateway_reference_depth continuation)destination->
  gateway_reference_place_value ge(Returnstate pointer(Kcall(Some destination)function environment temporaries continuation)memory)owner value->
  gateway_reference_place_value ge(State function Sskip continuation environment(PTree.set destination pointer temporaries)memory)owner value.
Proof.
  intros NOT_RESULT NOT_DESTINATION BOUND;destruct owner as[invocation identifier|object offset|invocation|invocation index|identifier].
  - cbn[gateway_reference_place_value gateway_reference_saved_temporary gateway_reference_depth]in BOUND|-*.
    destruct(Nat.eq_dec invocation(gateway_reference_depth continuation))as[SAME|DIFFERENT];[|exact BOUND].
    subst invocation;rewrite PTree.gso;[exact BOUND|intro SAME;subst identifier;apply NOT_DESTINATION;reflexivity].
  - exact BOUND.
  - destruct BOUND as[SAME VALUE];apply NOT_RESULT;subst invocation;reflexivity.
  - exact BOUND.
  - exact BOUND.
Qed.

Lemma gateway_reference_assigned_place_frame ge function body continuation environment temporaries pointer memory source destination owner value:
  owner<>gateway_reference_temporary(gateway_reference_depth continuation)source->
  owner<>gateway_reference_temporary(gateway_reference_depth continuation)destination->
  gateway_reference_place_value ge(State function body continuation environment temporaries memory)owner value->
  gateway_reference_place_value ge(State function Sskip continuation environment(PTree.set destination pointer temporaries)memory)owner value.
Proof.
  intros NOT_SOURCE NOT_DESTINATION BOUND;destruct owner as[invocation identifier|object offset|invocation|invocation index|identifier].
  - cbn[gateway_reference_place_value]in BOUND|-*.
    destruct(Nat.eq_dec invocation(gateway_reference_depth continuation))as[SAME|DIFFERENT];[|exact BOUND].
    subst invocation;rewrite PTree.gso;[exact BOUND|intro SAME;subst identifier;apply NOT_DESTINATION;reflexivity].
  - exact BOUND.
  - exact BOUND.
  - exact BOUND.
  - exact BOUND.
Qed.
