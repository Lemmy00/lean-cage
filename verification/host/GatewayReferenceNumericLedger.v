(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Selected operand cleanup vacates exactly its source place;
   independent references to the same pointer survive all other numeric operations. *)
From Stdlib Require Import List.
From compcert Require Import Values.
From HostGateway Require Import GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceNormalForm.
Import ListNotations.

Lemma gateway_reference_numeric_minted_keeps ledger final owner pointer previous ticket value:
  gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_owns ledger previous ticket value->gateway_reference_owns final previous ticket value.
Proof. intros MINT OWNED;destruct(gateway_reference_mint_entries _ _ _ _ MINT)as[ENTRIES NEXT].
  unfold gateway_reference_owns;rewrite ENTRIES;right;exact OWNED. Qed.

Theorem gateway_reference_numeric_released_vacant ledger final owner pointer:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_take owner(gateway_reference_entries final)=None.
Proof.
  intros[TICKETS[OWNERS BOUNDS]];unfold gateway_reference_apply.
  destruct(gateway_reference_take owner(gateway_reference_entries ledger))as[[selected remaining]|]eqn:TAKE;[|discriminate].
  destruct(Val.eq pointer(gateway_reference_pointer selected));[|discriminate].
  intro APPLY;injection APPLY as FINAL;subst final.
  destruct(gateway_reference_take_nodup gateway_reference_owner _ _ _ _ TAKE OWNERS)as[UNIQUE ABSENT].
  destruct(gateway_reference_take_decomposition _ _ _ _ TAKE)as(prefix &suffix &ENTRIES &REMAINING &OWNER).
  apply gateway_reference_take_none;intros entry MEMBER SAME;apply ABSENT;rewrite OWNER.
  apply in_map_iff;exists entry;split;[exact SAME|exact MEMBER].
Qed.

Theorem gateway_reference_numeric_released_keeps ledger final owner ticket pointer previous other value:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger owner ticket pointer->other<>ticket->
  gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_owns ledger previous other value->gateway_reference_owns final previous other value.
Proof.
  intros WELL OWNED DIFFERENT RELEASE OLD.
  destruct(gateway_reference_release_selected ledger owner ticket pointer WELL OWNED)
    as(selected &APPLY &SELECTED_WELL &ABSENT &RETAINED &COUNTS).
  rewrite RELEASE in APPLY;injection APPLY as SAME;subst selected;apply RETAINED;assumption.
Qed.
