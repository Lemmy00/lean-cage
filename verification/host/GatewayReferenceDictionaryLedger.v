(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A dictionary saves distinct owning source places for its parent
   and parsed key; pointer aliasing does not collapse those reference credits. *)
From Stdlib Require Import List PeanoNat Arith Lia.
From compcert Require Import Maps Values Memory Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceActivation
  GatewayReferenceStackBound GatewayReferenceNormalForm GatewayReferenceLoopLedger GatewayReferenceThreads.
Import ListNotations.

Definition gateway_reference_dictionary_entries context older ledger parent_ticket parent key_ticket key:Prop:=
  gateway_reference_entries ledger=
    gateway_reference_entry key_ticket(gateway_reference_temporary(gateway_reference_depth context)_first)key::
    gateway_reference_entry parent_ticket(gateway_reference_temporary(gateway_reference_depth context)_container)parent::
    gateway_reference_entries older.

Lemma gateway_reference_dictionary_free context older ledger parent_ticket parent key_ticket key identifier:
  gateway_reference_stack_bound context older->
  gateway_reference_dictionary_entries context older ledger parent_ticket parent key_ticket key->
  identifier<>_container->identifier<>_first->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)identifier)
    (gateway_reference_entries ledger)=None.
Proof.
  intros STACK ENTRIES PARENT KEY;apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite ENTRIES in MEMBER.
  destruct MEMBER as[SAME|[SAME|MEMBER]].
  - subst entry;cbn in OWNER;injection OWNER;congruence.
  - subst entry;cbn in OWNER;injection OWNER;congruence.
  - destruct(STACK entry MEMBER)as[invocation[old_identifier[OLD VALUE]]].
    rewrite OWNER in OLD;injection OLD;intros SAME_IDENTIFIER SAME_INVOCATION;subst invocation.
    rewrite gateway_reference_saved_above in VALUE by lia;discriminate.
Qed.

Theorem gateway_reference_dictionary_call_stack context older ledger parent_ticket parent key_ticket key
    destination function environment parameters local:
  gateway_reference_stack_bound context older->
  gateway_reference_dictionary_entries context older ledger parent_ticket parent key_ticket key->
  gateway_reference_depth local=0%nat->parameters!_container=Some parent->parameters!_first=Some key->
  gateway_reference_stack_bound(Kcall destination function environment parameters(plug_cont local context))ledger.
Proof.
  intros STACK ENTRIES LOCAL PARENT KEY entry MEMBER;rewrite ENTRIES in MEMBER.
  destruct MEMBER as[SAME|[SAME|MEMBER]].
  - subst entry;exists(gateway_reference_depth context),_first;split;[reflexivity|].
    cbn[gateway_reference_saved_temporary];rewrite gateway_reference_depth_plug,LOCAL;cbn.
    destruct(Nat.eq_dec(gateway_reference_depth context)(gateway_reference_depth context));[exact KEY|congruence].
  - subst entry;exists(gateway_reference_depth context),_container;split;[reflexivity|].
    cbn[gateway_reference_saved_temporary];rewrite gateway_reference_depth_plug,LOCAL;cbn.
    destruct(Nat.eq_dec(gateway_reference_depth context)(gateway_reference_depth context));[exact PARENT|congruence].
  - destruct(STACK entry MEMBER)as[invocation[identifier[OWNER VALUE]]].
    exists invocation,identifier;split;[exact OWNER|].
    assert(BELOW:(invocation<gateway_reference_depth context)%nat).
    { destruct(le_lt_dec(gateway_reference_depth context)invocation);[|exact l].
      rewrite gateway_reference_saved_above in VALUE by exact l;discriminate. }
    cbn[gateway_reference_saved_temporary];rewrite gateway_reference_depth_plug,LOCAL;cbn.
    destruct(Nat.eq_dec invocation(gateway_reference_depth context));[lia|].
    rewrite gateway_reference_saved_under_plug by exact BELOW;exact VALUE.
Qed.

Theorem gateway_reference_dictionary_call_bound ge context older ledger parent_ticket parent key_ticket key
    local definition arguments destination function environment parameters memory:
  gateway_reference_stack_bound context older->
  gateway_reference_dictionary_entries context older ledger parent_ticket parent key_ticket key->
  gateway_reference_depth local=0%nat->parameters!_container=Some parent->parameters!_first=Some key->
  gateway_reference_source_bound ge
    (Callstate definition arguments(Kcall destination function environment parameters(plug_cont local context))memory)ledger.
Proof.
  intros STACK ENTRIES LOCAL PARENT KEY;apply gateway_reference_stack_call_bound.
  eapply gateway_reference_dictionary_call_stack;eassumption.
Qed.
