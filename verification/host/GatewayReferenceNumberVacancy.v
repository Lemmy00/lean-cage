(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The exact retained numeric head entries preserve fresh
   caller/source places without requiring their object pointers to be distinct. *)
From Stdlib Require Import List.
From compcert Require Import Values.
From HostGateway Require Import GatewayReferenceLedger GatewayReferenceNormalForm.
Import ListNotations.

Lemma gateway_number_two_heads_vacant place first_owner first_ticket first second_owner second_ticket second entries:
  first_owner<>place->second_owner<>place->gateway_reference_take place entries=None->
  gateway_reference_take place(gateway_reference_entry first_ticket first_owner first::gateway_reference_entry second_ticket second_owner second::entries)=None.
Proof.
  intros FIRST SECOND VACANT;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
  destruct(gateway_reference_place_eq place first_owner);[congruence|].
  destruct(gateway_reference_place_eq place second_owner);[congruence|rewrite VACANT;reflexivity].
Qed.

Lemma gateway_number_one_head_vacant place owner ticket pointer entries:
  owner<>place->gateway_reference_take place entries=None->
  gateway_reference_take place(gateway_reference_entry ticket owner pointer::entries)=None.
Proof.
  intros DIFFERENT VACANT;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
  destruct(gateway_reference_place_eq place owner);[congruence|rewrite VACANT;reflexivity].
Qed.
