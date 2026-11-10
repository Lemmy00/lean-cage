(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Numeric temporaries may alias cached object pointers; cleanup
   removes the selected source place while retaining the other minted reference. *)
From Stdlib Require Import List.
From compcert Require Import Values.
From HostGateway Require Import GatewayReferenceLedger GatewayReferenceNormalForm.
Import ListNotations.

Lemma gateway_reference_numeric_middle_release ledger final tail first_ticket first_owner first_pointer ticket owner pointer:
  owner<>first_owner->
  gateway_reference_entries ledger=gateway_reference_entry first_ticket first_owner first_pointer::gateway_reference_entry ticket owner pointer::tail->
  gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_entries final=gateway_reference_entry first_ticket first_owner first_pointer::tail /\
  gateway_reference_next final=gateway_reference_next ledger.
Proof.
  intros DIFFERENT ENTRIES;unfold gateway_reference_apply;rewrite ENTRIES.
  cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner gateway_reference_pointer gateway_reference_ticket].
  destruct(gateway_reference_place_eq owner first_owner);[congruence|].
  destruct(gateway_reference_place_eq owner owner);[|congruence].
  cbn[gateway_reference_pointer gateway_reference_entry].
  destruct(Val.eq pointer pointer);[|congruence].
  intro SAME;injection SAME as FINAL;subst final;split;reflexivity.
Qed.
