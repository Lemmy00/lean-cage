(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Dictionary cleanup consumes the selected key and value places;
   identical object pointers retain their independent source reference credits. *)
From Stdlib Require Import List.
From compcert Require Import Values Clight.
From HostGateway Require Import GatewaySource GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceNormalForm.
Import ListNotations.

Lemma gateway_reference_dictionary_key_release context ledger final tail key_ticket key child_ticket child:
  gateway_reference_entries ledger=
    gateway_reference_entry child_ticket(gateway_reference_temporary(gateway_reference_depth context)_value__1)child::
    gateway_reference_entry key_ticket(gateway_reference_temporary(gateway_reference_depth context)_first)key::tail->
  gateway_reference_apply(gateway_reference_release(gateway_reference_temporary(gateway_reference_depth context)_first)key)
    (gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_entries final=
    gateway_reference_entry child_ticket(gateway_reference_temporary(gateway_reference_depth context)_value__1)child::tail /\
  gateway_reference_next final=gateway_reference_next ledger.
Proof.
  intros ENTRIES;unfold gateway_reference_apply;rewrite ENTRIES.
  cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner gateway_reference_pointer gateway_reference_ticket].
  destruct(gateway_reference_place_eq(gateway_reference_temporary(gateway_reference_depth context)_first)
    (gateway_reference_temporary(gateway_reference_depth context)_value__1));[discriminate|].
  destruct(gateway_reference_place_eq(gateway_reference_temporary(gateway_reference_depth context)_first)
    (gateway_reference_temporary(gateway_reference_depth context)_first));[|congruence].
  cbn[gateway_reference_pointer gateway_reference_entry].
  destruct(Val.eq key key);[|congruence].
  intro SAME;injection SAME as FINAL;subst final;split;reflexivity.
Qed.
