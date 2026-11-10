(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A completed recursive child adds one selected result owner to the
   same older caller entries; later source moves/releases preserve that exact tail. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceStackBound.
Import ListNotations.

Definition gateway_reference_entry ticket owner pointer:gateway_owned_reference:={|
  gateway_reference_ticket:=ticket;gateway_reference_owner:=owner;gateway_reference_pointer:=pointer|}.
Definition gateway_reference_result_entries context initial final ticket pointer:Prop:=
  gateway_reference_entries final=
    gateway_reference_entry ticket(gateway_reference_result(gateway_reference_depth context))pointer::gateway_reference_entries initial.

Lemma gateway_reference_mint_entries ledger final owner pointer:
  gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_entries final=gateway_reference_entry(gateway_reference_next ledger)owner pointer::gateway_reference_entries ledger /\
  gateway_reference_next final=S(gateway_reference_next ledger).
Proof.
  unfold gateway_reference_apply;destruct(gateway_reference_take owner(gateway_reference_entries ledger))as[[selected remaining]|];[discriminate|].
  intro SAME;injection SAME as FINAL;subst final;split;reflexivity.
Qed.

Lemma gateway_reference_head_move ledger final tail ticket owner to pointer:
  gateway_reference_entries ledger=gateway_reference_entry ticket owner pointer::tail->
  gateway_reference_apply(gateway_reference_move owner to)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_entries final=gateway_reference_entry ticket to pointer::tail /\
  gateway_reference_next final=gateway_reference_next ledger.
Proof.
  intros ENTRIES;unfold gateway_reference_apply;rewrite ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner gateway_reference_pointer gateway_reference_ticket].
  destruct(gateway_reference_place_eq owner owner);[|congruence].
  destruct(gateway_reference_take to tail)as[[selected remaining]|];[discriminate|].
  intro SAME;injection SAME as FINAL;subst final;split;reflexivity.
Qed.

Lemma gateway_reference_head_release ledger final tail ticket owner pointer:
  gateway_reference_entries ledger=gateway_reference_entry ticket owner pointer::tail->
  gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_entries final=tail /\gateway_reference_next final=gateway_reference_next ledger.
Proof.
  intros ENTRIES;unfold gateway_reference_apply;rewrite ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner gateway_reference_pointer gateway_reference_ticket].
  destruct(gateway_reference_place_eq owner owner);[|congruence].
  cbn[gateway_reference_pointer gateway_reference_entry].
  destruct(Val.eq pointer pointer);[|congruence].
  intro SAME;injection SAME as FINAL;subst final;split;reflexivity.
Qed.

Theorem gateway_reference_result_entries_bound ge context initial final ticket pointer memory:
  gateway_reference_stack_bound context initial->gateway_reference_result_entries context initial final ticket pointer->
  gateway_reference_source_bound ge(Returnstate pointer context memory)final.
Proof.
  intros STACK ENTRIES entry MEMBER;unfold gateway_reference_result_entries in ENTRIES;rewrite ENTRIES in MEMBER.
  destruct MEMBER as[SAME|MEMBER].
  - subst entry;apply gateway_reference_result_binding.
  - destruct(STACK entry MEMBER)as[invocation[identifier[OWNER VALUE]]].
    rewrite OWNER;exact VALUE.
Qed.

Lemma gateway_reference_result_entries_old context initial final ticket pointer:
  gateway_reference_result_entries context initial final ticket pointer->
  forall entry,In entry(gateway_reference_entries initial)->In entry(gateway_reference_entries final).
Proof. intros ENTRIES entry MEMBER;unfold gateway_reference_result_entries in ENTRIES;rewrite ENTRIES;right;exact MEMBER. Qed.
