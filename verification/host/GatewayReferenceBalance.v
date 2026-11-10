(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Retained and retired references may alias new parser values;
   aggregate accounting composes actual count deltas without adding separate FIT inequalities. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceNormalForm GatewayReferenceRuntime.
Import ListNotations.

Definition gateway_reference_balance(before after:python_world)(initial final:gateway_reference_ledger):Prop:=
  forall pointer,(python_native_strong before pointer+gateway_reference_count final pointer<=
    python_native_strong after pointer+gateway_reference_count initial pointer)%nat.

Lemma gateway_reference_balance_refl python ledger:gateway_reference_balance python python ledger ledger.
Proof. intro pointer;lia. Qed.
Lemma gateway_reference_balance_trans first second third initial middle final:
  gateway_reference_balance first second initial middle->gateway_reference_balance second third middle final->
  gateway_reference_balance first third initial final.
Proof. intros FIRST SECOND pointer;specialize(FIRST pointer);specialize(SECOND pointer);lia. Qed.
Lemma gateway_reference_balance_retained before after ledger:
  (forall pointer,(python_native_strong before pointer<=python_native_strong after pointer)%nat)->
  gateway_reference_balance before after ledger ledger.
Proof. intros RETAINED pointer;specialize(RETAINED pointer);lia. Qed.

Theorem gateway_reference_balance_reservations before after initial final(reserved:Values.val->nat):
  (forall pointer,(reserved pointer+gateway_reference_count initial pointer<=python_native_strong before pointer)%nat)->
  gateway_reference_balance before after initial final->
  forall pointer,(reserved pointer+gateway_reference_count final pointer<=python_native_strong after pointer)%nat.
Proof. intros FIT BALANCE pointer;specialize(FIT pointer);specialize(BALANCE pointer);lia. Qed.

Theorem gateway_reference_balance_mint before after initial final owner pointer:
  gateway_reference_credit before after pointer->
  gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid initial)=gateway_reference_valid final->
  gateway_reference_balance before after initial final.
Proof.
  intros CREDIT APPLY;destruct(gateway_reference_mint_entries initial final owner pointer APPLY)as[ENTRIES NEXT].
  intro other;unfold gateway_reference_count;rewrite ENTRIES;cbn.
  destruct(Val.eq pointer other)as[SAME|DIFFERENT].
  - subst other;rewrite(gateway_reference_credit_target _ _ _ CREDIT);lia.
  - rewrite(gateway_reference_credit_other _ _ _ CREDIT other ltac:(congruence));lia.
Qed.

Theorem gateway_reference_balance_release before after initial final owner ticket pointer:
  gateway_reference_ledger_well_formed initial->gateway_reference_owns initial owner ticket pointer->
  gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid initial)=gateway_reference_valid final->
  python_native_strong before pointer=S(python_native_strong after pointer)->
  gateway_native_references_frame before after[pointer]->gateway_reference_balance before after initial final.
Proof.
  intros FORMED OWNED APPLY DEBIT OTHERS.
  destruct(gateway_reference_release_selected initial owner ticket pointer FORMED OWNED)
    as(selected &SELECTED &WELL &ABSENT &RETAINED &COUNTS).
  rewrite APPLY in SELECTED;injection SELECTED as SAME;subst selected.
  intro other;rewrite(COUNTS other);destruct(Val.eq pointer other)as[SAME|DIFFERENT].
  - subst other;rewrite DEBIT;lia.
  - rewrite(OTHERS other ltac:(intros[SAME|EMPTY];[congruence|contradiction]));lia.
Qed.

Theorem gateway_reference_balance_move before after initial final from to ticket pointer:
  gateway_reference_ledger_well_formed initial->gateway_reference_owns initial from ticket pointer->
  (forall entry,In entry(gateway_reference_entries initial)->gateway_reference_owner entry=to->gateway_reference_ticket entry=ticket)->
  gateway_reference_apply(gateway_reference_move from to)(gateway_reference_valid initial)=gateway_reference_valid final->
  (forall pointer,(python_native_strong before pointer<=python_native_strong after pointer)%nat)->
  gateway_reference_balance before after initial final.
Proof.
  intros FORMED OWNED VACANT APPLY RETAIN.
  destruct(gateway_reference_move_selected initial from to ticket pointer FORMED OWNED VACANT)
    as(selected &SELECTED &WELL &CAPTURED &OTHERS &COUNTS).
  rewrite APPLY in SELECTED;injection SELECTED as SAME;subst selected.
  intro other;rewrite(COUNTS other);specialize(RETAIN other);lia.
Qed.
