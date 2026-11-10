(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The six actual numeric mint/release actions replace the old
   value entry with one new value and preserve the exact older reference tail. *)
From Stdlib Require Import List.
From compcert Require Import Values.
From HostGateway Require Import GatewaySource GatewayReferenceLedger GatewayReferenceNormalForm GatewayReferenceNumericNormalForm GatewayReferenceNumberOwners.
Import ListNotations.

Lemma gateway_number_release_current_under_operands invocation ledger final entries remaining current_ticket current
    first_ticket first second_ticket second:
  gateway_reference_entries ledger=
    gateway_reference_entry first_ticket(number_scaled_owner invocation)first::
    gateway_reference_entry second_ticket(number_part_owner invocation)second::entries->
  gateway_reference_take(number_current_owner invocation)entries=
    Some(gateway_reference_entry current_ticket(number_current_owner invocation)current,remaining)->
  gateway_reference_apply(gateway_reference_release(number_current_owner invocation)current)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_entries final=
    gateway_reference_entry first_ticket(number_scaled_owner invocation)first::
    gateway_reference_entry second_ticket(number_part_owner invocation)second::remaining.
Proof.
  intros ENTRIES TAKE;unfold gateway_reference_apply;rewrite ENTRIES.
  cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner gateway_reference_pointer gateway_reference_ticket].
  destruct(gateway_reference_place_eq(number_current_owner invocation)(number_scaled_owner invocation));[discriminate|].
  destruct(gateway_reference_place_eq(number_current_owner invocation)(number_part_owner invocation));[discriminate|].
  rewrite TAKE;cbn[gateway_reference_pointer gateway_reference_entry].
  destruct(Val.eq current current);[|congruence].
  intro APPLY;injection APPLY as SAME;subst final;reflexivity.
Qed.

Theorem gateway_number_iteration_reference_tail invocation initial part_ledger scaled_ledger released summed_ledger scaled_released final
    tail ticket current part scaled summed:
  gateway_reference_take(number_current_owner invocation)(gateway_reference_entries initial)=
    Some(gateway_reference_entry ticket(number_current_owner invocation)current,tail)->
  gateway_reference_apply(gateway_reference_mint(number_part_owner invocation)part)(gateway_reference_valid initial)=gateway_reference_valid part_ledger->
  gateway_reference_apply(gateway_reference_mint(number_scaled_owner invocation)scaled)(gateway_reference_valid part_ledger)=gateway_reference_valid scaled_ledger->
  gateway_reference_apply(gateway_reference_release(number_current_owner invocation)current)(gateway_reference_valid scaled_ledger)=gateway_reference_valid released->
  gateway_reference_apply(gateway_reference_mint(number_current_owner invocation)summed)(gateway_reference_valid released)=gateway_reference_valid summed_ledger->
  gateway_reference_apply(gateway_reference_release(number_scaled_owner invocation)scaled)(gateway_reference_valid summed_ledger)=gateway_reference_valid scaled_released->
  gateway_reference_apply(gateway_reference_release(number_part_owner invocation)part)(gateway_reference_valid scaled_released)=gateway_reference_valid final->
  gateway_reference_entries final=
    gateway_reference_entry(gateway_reference_next released)(number_current_owner invocation)summed::tail.
Proof.
  intros TAKE PART SCALED RELEASE SUM RELEASE_SCALED RELEASE_PART.
  destruct(gateway_reference_mint_entries _ _ _ _ PART)as[PART_ENTRIES PART_NEXT].
  destruct(gateway_reference_mint_entries _ _ _ _ SCALED)as[SCALED_ENTRIES SCALED_NEXT].
  assert(RELEASED:gateway_reference_entries released=
    gateway_reference_entry(gateway_reference_next part_ledger)(number_scaled_owner invocation)scaled::
    gateway_reference_entry(gateway_reference_next initial)(number_part_owner invocation)part::tail).
  { eapply gateway_number_release_current_under_operands;
      [rewrite SCALED_ENTRIES,PART_ENTRIES;reflexivity|exact TAKE|exact RELEASE]. }
  destruct(gateway_reference_mint_entries _ _ _ _ SUM)as[SUM_ENTRIES SUM_NEXT].
  destruct(gateway_reference_numeric_middle_release summed_ledger scaled_released
    (gateway_reference_entry(gateway_reference_next initial)(number_part_owner invocation)part::tail)
    (gateway_reference_next released)(number_current_owner invocation)summed
    (gateway_reference_next part_ledger)(number_scaled_owner invocation)scaled ltac:(discriminate)
    ltac:(rewrite SUM_ENTRIES,RELEASED;reflexivity)RELEASE_SCALED)as[AFTER_SCALED NEXT].
  destruct(gateway_reference_numeric_middle_release scaled_released final tail
    (gateway_reference_next released)(number_current_owner invocation)summed
    (gateway_reference_next initial)(number_part_owner invocation)part ltac:(discriminate)
    AFTER_SCALED RELEASE_PART)as[FINAL NEXT_FINAL];exact FINAL.
Qed.
