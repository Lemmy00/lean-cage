(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Moving a selected second credit preserves the
   first credit and exact older tail, including aliases of their pointer values. *)
From Stdlib Require Import List.
From compcert Require Import Values.
From HostGateway Require Import GatewayReferenceLedger GatewayReferenceNormalForm.
Import ListNotations.

Lemma gateway_reference_second_move ledger final tail first_ticket first_owner first_pointer ticket owner target pointer:
  first_owner<>owner->
  gateway_reference_entries ledger=gateway_reference_entry first_ticket first_owner first_pointer::gateway_reference_entry ticket owner pointer::tail->
  gateway_reference_apply(gateway_reference_move owner target)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_entries final=gateway_reference_entry ticket target pointer::gateway_reference_entry first_ticket first_owner first_pointer::tail /\
  gateway_reference_next final=gateway_reference_next ledger.
Proof.
  intros DISTINCT ENTRIES;unfold gateway_reference_apply;rewrite ENTRIES.
  cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner gateway_reference_pointer gateway_reference_ticket].
  destruct(gateway_reference_place_eq owner first_owner);[congruence|].
  destruct(gateway_reference_place_eq owner owner);[|congruence].
  cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
  destruct(gateway_reference_place_eq target first_owner);[discriminate|].
  destruct(gateway_reference_take target tail)as[[selected rest]|];[discriminate|].
  intro SAME;injection SAME as FINAL;subst final;split;reflexivity.
Qed.
