(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Container loop owners bind the real saved parent/child values;
   recursive returns and selected releases retain the same older invocation entries. *)
From Stdlib Require Import List PeanoNat Arith Lia.
From compcert Require Import Maps Integers Values Memory Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayValueEntry GatewayContainerLoopSource GatewayContainerArraySource
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceActivation GatewayReferenceStackBound
  GatewayReferenceNormalForm GatewayReferenceChildOwnership GatewayReferenceThreads GatewayReferenceMoves.
Import ListNotations.

Definition gateway_reference_loop_entries context older ledger parent_ticket parent:Prop:=
  gateway_reference_entries ledger=gateway_reference_entry parent_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_container)parent::gateway_reference_entries older.

Lemma gateway_reference_loop_free context older ledger parent_ticket parent identifier:
  gateway_reference_stack_bound context older->gateway_reference_loop_entries context older ledger parent_ticket parent->
  identifier<>_container->gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)identifier)
    (gateway_reference_entries ledger)=None.
Proof.
  intros STACK ENTRIES DIFFERENT.
  apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite ENTRIES in MEMBER.
  destruct MEMBER as[SAME|MEMBER].
  - subst entry;cbn in OWNER;injection OWNER;congruence.
  - destruct(STACK entry MEMBER)as[invocation[old_identifier[OLD VALUE]]].
    rewrite OWNER in OLD;injection OLD;intros SAME_IDENTIFIER SAME_INVOCATION;subst invocation.
    rewrite gateway_reference_saved_above in VALUE by lia;discriminate.
Qed.

Theorem gateway_reference_loop_child_stack context older ledger parent_ticket parent slots parameters:
  gateway_reference_stack_bound context older->gateway_reference_loop_entries context older ledger parent_ticket parent->
  parameters!_container=Some parent->
  gateway_reference_stack_bound(plug_cont(gateway_container_first_cont slots parameters)context)ledger.
Proof.
  intros STACK ENTRIES PARENT entry MEMBER;rewrite ENTRIES in MEMBER;destruct MEMBER as[SAME|MEMBER].
  - subst entry;exists(gateway_reference_depth context),_container;split;[reflexivity|].
    cbn[gateway_container_first_cont plug_cont gateway_reference_saved_temporary].
    cbn[gateway_reference_depth gateway_container_loop_cont].
    destruct(Nat.eq_dec _ _);[exact PARENT|exfalso;apply n;rewrite gateway_reference_depth_plug;reflexivity].
  - destruct(STACK entry MEMBER)as[invocation[identifier[OWNER VALUE]]].
    exists invocation,identifier;split;[exact OWNER|].
    assert(BELOW:(invocation<gateway_reference_depth context)%nat).
    { destruct(le_lt_dec(gateway_reference_depth context)invocation);[|exact l].
      rewrite gateway_reference_saved_above in VALUE by exact l;discriminate. }
    rewrite gateway_reference_saved_under_plug by exact BELOW;exact VALUE.
Qed.

Theorem gateway_reference_loop_call_bound ge context older ledger parent_ticket parent local definition arguments destination function environment parameters memory:
  gateway_reference_stack_bound context older->gateway_reference_loop_entries context older ledger parent_ticket parent->
  gateway_reference_depth local=0%nat->parameters!_container=Some parent->
  gateway_reference_source_bound ge
    (Callstate definition arguments(Kcall destination function environment parameters(plug_cont local context))memory)ledger.
Proof.
  intros STACK ENTRIES LOCAL PARENT entry MEMBER;rewrite ENTRIES in MEMBER;destruct MEMBER as[SAME|MEMBER].
  - subst entry;cbn[gateway_reference_place_value gateway_reference_saved_temporary gateway_reference_owner gateway_reference_pointer gateway_reference_entry].
    rewrite gateway_reference_depth_plug,LOCAL;cbn.
    destruct(Nat.eq_dec(gateway_reference_depth context)(gateway_reference_depth context));[exact PARENT|congruence].
  - destruct(STACK entry MEMBER)as[invocation[identifier[OWNER VALUE]]].
    rewrite OWNER;unfold gateway_reference_place_value;cbn[gateway_reference_saved_temporary].
    rewrite gateway_reference_depth_plug,LOCAL;cbn.
    destruct(Nat.eq_dec invocation(gateway_reference_depth context))as[SAME|OTHER].
    + subst invocation;rewrite gateway_reference_saved_above in VALUE by lia;discriminate.
    + assert(BELOW:(invocation<gateway_reference_depth context)%nat).
      { destruct(le_lt_dec(gateway_reference_depth context)invocation);[|exact l].
        rewrite gateway_reference_saved_above in VALUE by exact l;discriminate. }
      rewrite gateway_reference_saved_under_plug by exact BELOW;exact VALUE.
Qed.
