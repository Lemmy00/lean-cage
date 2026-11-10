(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real caller frames distinguish recursive parser owners. *)
From Stdlib Require Import List PeanoNat Lia.
From compcert Require Import Maps AST Values Memory Clight.
Require Import CallContexts.
From HostGateway Require Import GatewayReferenceLedger GatewayReferencePlaces.
Import ListNotations.

Lemma gateway_reference_depth_plug local context:
  gateway_reference_depth(plug_cont local context)=
    gateway_reference_depth local+gateway_reference_depth context.
Proof. induction local;cbn;lia. Qed.

Lemma gateway_reference_saved_above continuation invocation identifier:
  (gateway_reference_depth continuation<=invocation)%nat->
  gateway_reference_saved_temporary continuation invocation identifier=None.
Proof.
  induction continuation;cbn;intro ABOVE;try reflexivity;try(apply IHcontinuation;exact ABOVE).
  destruct(Nat.eq_dec invocation(gateway_reference_depth continuation));[lia|].
  apply IHcontinuation;lia.
Qed.

Theorem gateway_reference_fresh_call_places(ge:Clight.genv)definition arguments continuation memory ledger:
  gateway_reference_source_bound ge(Callstate definition arguments continuation memory)ledger->
  (forall identifier invocation,(gateway_reference_depth continuation<=invocation)%nat->
    gateway_reference_take(gateway_reference_temporary invocation identifier)(gateway_reference_entries ledger)=None) /\
  (forall invocation,gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries ledger)=None).
Proof.
  intro BOUND;split.
  - intros identifier invocation ABOVE;apply gateway_reference_take_none;intros entry MEMBER OWNER.
    pose proof(BOUND entry MEMBER)as VALUE;rewrite OWNER in VALUE.
    change(gateway_reference_saved_temporary continuation invocation identifier=Some(gateway_reference_pointer entry))in VALUE.
    rewrite gateway_reference_saved_above in VALUE by exact ABOVE;discriminate.
  - intro invocation;apply gateway_reference_take_none;intros entry MEMBER OWNER.
    pose proof(BOUND entry MEMBER)as VALUE;rewrite OWNER in VALUE;exact VALUE.
Qed.
