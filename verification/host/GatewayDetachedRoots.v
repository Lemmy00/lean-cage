(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: A real strong Python root retains its allocation after GIL
   release. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values Memory Integers.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceThreads GatewayReferenceContainerScope GatewayReferenceGraphCapture.
Import ListNotations.

(* This is CPython allocation lifetime, not managed-byte immutability or held
   interpreter readiness. The caller must derive its selected positive credit. *)
Definition gateway_detached_root_lifetime {World}(python:World->python_world)
    (detached:Values.val->mem->World->Prop):Prop:=
  forall saved memory world pointer,detached saved memory world->
    (0<python_native_strong(python world)pointer)%nat->
    exists object offset,pointer=Vptr object offset /\Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true.

Theorem gateway_actual_owned_detached_pointer {World}python detached
    (lifetime:@gateway_detached_root_lifetime World python detached)
    saved ledger place ticket pointer memory world:
  detached saved memory world->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger place ticket pointer->
  exists object offset,pointer=Vptr object offset /\Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true.
Proof.
  intros DETACHED FIT OWNED;apply(lifetime saved memory world pointer DETACHED).
  pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(FIT pointer);lia.
Qed.

Theorem gateway_actual_captured_detached_pointer {World}python objects detached decimal_float
    (lifetime:@gateway_detached_root_lifetime World python detached)
    saved ledger held ticket pointer wire snapshot memory world:
  detached saved memory world->gateway_reference_scope python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture ticket pointer wire snapshot)held->
  exists object offset,pointer=Vptr object offset /\Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true.
Proof.
  intros DETACHED SCOPE MEMBER.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[[place OWNED]REST].
  eapply gateway_actual_owned_detached_pointer;[exact lifetime|exact DETACHED|exact(proj1 SCOPE)|exact OWNED].
Qed.
