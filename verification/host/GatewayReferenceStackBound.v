(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Recursive parser references remain bound to the real saved caller
   temporaries; new local activations do not forge or overwrite them. *)
From Stdlib Require Import List PeanoNat Arith Lia.
From compcert Require Import Maps Values Memory Clight.
Require Import CallContexts.
From HostGateway Require Import GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceActivation GatewayReferenceFrames.
Import ListNotations.

Definition gateway_reference_temporaries_only ledger:Prop:=
  forall entry,In entry(gateway_reference_entries ledger)->exists invocation identifier,
    gateway_reference_owner entry=gateway_reference_temporary invocation identifier.
Definition gateway_reference_stack_bound context ledger:Prop:=
  forall entry,In entry(gateway_reference_entries ledger)->exists invocation identifier,
    gateway_reference_owner entry=gateway_reference_temporary invocation identifier /\
    gateway_reference_saved_temporary context invocation identifier=Some(gateway_reference_pointer entry).

Lemma gateway_reference_saved_under_plug local context invocation identifier:
  (invocation<gateway_reference_depth context)%nat->
  gateway_reference_saved_temporary(plug_cont local context)invocation identifier=
    gateway_reference_saved_temporary context invocation identifier.
Proof.
  intro BELOW;induction local;cbn;try exact IHlocal;try reflexivity.
  rewrite gateway_reference_depth_plug.
  destruct(Nat.eq_dec invocation(gateway_reference_depth local+gateway_reference_depth context));[lia|exact IHlocal].
Qed.

Lemma gateway_reference_stack_call_bound ge definition arguments context memory ledger:
  gateway_reference_stack_bound context ledger->
  gateway_reference_source_bound ge(Callstate definition arguments context memory)ledger.
Proof.
  intros STACK entry MEMBER;destruct(STACK entry MEMBER)as[invocation[identifier[OWNER VALUE]]].
  rewrite OWNER;exact VALUE.
Qed.

Lemma gateway_reference_temporary_call_stack ge definition arguments context memory ledger:
  gateway_reference_temporaries_only ledger->gateway_reference_source_bound ge(Callstate definition arguments context memory)ledger->
  gateway_reference_stack_bound context ledger.
Proof.
  intros TEMPORARIES BOUND entry MEMBER;destruct(TEMPORARIES entry MEMBER)as[invocation[identifier OWNER]].
  exists invocation,identifier;split;[exact OWNER|].
  pose proof(BOUND entry MEMBER)as VALUE;rewrite OWNER in VALUE;exact VALUE.
Qed.

Theorem gateway_reference_stack_local_bound ge context ledger local:
  gateway_reference_stack_bound context ledger->
  forall function body environment temporaries memory,
    gateway_reference_source_bound ge(State function body(plug_cont local context)environment temporaries memory)ledger.
Proof.
  intros STACK function body environment temporaries memory entry MEMBER.
  destruct(STACK entry MEMBER)as[invocation[identifier[OWNER VALUE]]].
  assert(BELOW:(invocation<gateway_reference_depth context)%nat).
  { destruct(le_lt_dec(gateway_reference_depth context)invocation);[|exact l].
    rewrite gateway_reference_saved_above in VALUE by exact l;discriminate. }
  rewrite OWNER;unfold gateway_reference_place_value.
  rewrite gateway_reference_depth_plug.
  destruct(Nat.eq_dec invocation(gateway_reference_depth local+gateway_reference_depth context));[lia|].
  rewrite gateway_reference_saved_under_plug by exact BELOW;exact VALUE.
Qed.

Theorem gateway_reference_stack_nested_call_bound ge context ledger local definition arguments memory:
  gateway_reference_stack_bound context ledger->
  gateway_reference_source_bound ge(Callstate definition arguments(plug_cont local context)memory)ledger.
Proof.
  intros STACK entry MEMBER;destruct(STACK entry MEMBER)as[invocation[identifier[OWNER VALUE]]].
  assert(BELOW:(invocation<gateway_reference_depth context)%nat).
  { destruct(le_lt_dec(gateway_reference_depth context)invocation);[|exact l].
    rewrite gateway_reference_saved_above in VALUE by exact l;discriminate. }
  rewrite OWNER;unfold gateway_reference_place_value;rewrite gateway_reference_saved_under_plug by exact BELOW;exact VALUE.
Qed.

Theorem gateway_reference_source_save_stack ge ledger function body continuation environment temporaries memory destination:
  gateway_reference_temporaries_only ledger->
  gateway_reference_source_bound ge(State function body continuation environment temporaries memory)ledger->
  gateway_reference_stack_bound(Kcall destination function environment temporaries continuation)ledger.
Proof.
  intros ONLY BOUND entry MEMBER;destruct(ONLY entry MEMBER)as[invocation[identifier OWNER]].
  exists invocation,identifier;split;[exact OWNER|]. pose proof(BOUND entry MEMBER)as VALUE.
  rewrite OWNER in VALUE;exact VALUE.
Qed.

Lemma gateway_reference_empty_stack context:
  gateway_reference_stack_bound context {|gateway_reference_next:=0;gateway_reference_entries:=[]|}.
Proof. intros entry MEMBER;contradiction. Qed.

Theorem gateway_reference_mint_local_bound ge context ledger final function body local environment temporaries memory identifier pointer:
  call_cont local=Kstop->gateway_reference_stack_bound context ledger->temporaries!identifier=Some pointer->
  gateway_reference_apply(gateway_reference_mint(gateway_reference_temporary(gateway_reference_depth context)identifier)pointer)
    (gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_source_bound ge(plug_state(State function body local environment temporaries memory)context)final.
Proof.
  intros STOP STACK VALUE MINT.
  unfold gateway_reference_apply in MINT.
  destruct(gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)identifier)
    (gateway_reference_entries ledger))as[[existing remaining]|]eqn:TAKE;[discriminate|].
  injection MINT as SAME;subst final.
  intros entry MEMBER;destruct MEMBER as[SAME|MEMBER].
  - subst entry;cbn[gateway_reference_owner gateway_reference_pointer].
    change(gateway_reference_place_value ge
      (State function body(plug_cont local context)environment temporaries memory)
      (gateway_reference_temporary(gateway_reference_depth context)identifier)pointer).
    assert(DEPTH:gateway_reference_depth(plug_cont local context)=gateway_reference_depth context).
    { rewrite gateway_reference_depth_plug.
      pose proof(gateway_reference_call_cont_depth local)as DEPTH;rewrite STOP in DEPTH;cbn in DEPTH;lia. }
    rewrite<-DEPTH;apply gateway_reference_temporary_binding;exact VALUE.
  - eapply gateway_reference_stack_local_bound;[exact STACK|exact MEMBER].
Qed.

Lemma gateway_reference_mint_keeps_vacant ledger final owner pointer other:
  gateway_reference_take other(gateway_reference_entries ledger)=None->owner<>other->
  gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_take other(gateway_reference_entries final)=None.
Proof.
  intros VACANT DIFFERENT;unfold gateway_reference_apply.
  destruct(gateway_reference_take owner(gateway_reference_entries ledger))as[[entry remaining]|]eqn:TAKE;[discriminate|].
  intro SAME;injection SAME as FINAL;subst final;cbn.
  destruct(gateway_reference_place_eq other owner);[congruence|rewrite VACANT;reflexivity].
Qed.
