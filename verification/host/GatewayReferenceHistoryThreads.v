(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Retain active and archived aliased holders together. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Values Memory Integers Floats.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayThreadRuntime
  GatewayNativeMemory GatewayThreadInvariant GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceHistory GatewayReferenceAbandon GatewayReferenceThreads.
Local Close Scope lean_scope.

Definition gateway_reference_history_scope {World} (python : World -> python_world)
    (objects : World -> gateway_object_heap) decimal_float ledger retired held world : Prop :=
  gateway_history_counts_fit ledger retired (python world) /\
  gateway_reference_scope python objects decimal_float ledger held world.

Theorem gateway_reference_history_scope_effect {World} python objects decimal_float ledger retired held world next :
  @gateway_reference_history_scope World python objects decimal_float ledger retired held world ->
  gateway_reference_thread_effect python objects world next ->
  gateway_reference_history_scope python objects decimal_float ledger retired held next.
Proof.
  intros [FIT SCOPE] EFFECT; split.
  - intro pointer; specialize (FIT pointer).
    pose proof (gateway_reference_thread_counts _ _ _ _ EFFECT pointer); lia.
  - eapply gateway_reference_scope_thread_effect; eassumption.
Qed.

Theorem gateway_reference_history_thread_invariant {World Event} (backend : gateway_backend World Event)
    native stable base heap_allocation python objects
    (contract : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    decimal_float ledger retired held :
  gateway_thread_invariant_contract backend native stable base heap_allocation
    (gateway_reference_history_scope python objects decimal_float ledger retired held).
Proof.
  constructor.
  - intros mode before world after next SIDE SCOPE AMBIENT.
    eapply gateway_reference_history_scope_effect; [exact SCOPE |].
    eapply gateway_reference_thread_ambient; [exact contract |exact SIDE |exact AMBIENT].
  - intros mode before world after_mode after next SCOPE OPERATION.
    eapply gateway_reference_history_scope_effect; [exact SCOPE |].
    eapply gateway_reference_thread_return; [exact contract |exact OPERATION].
Qed.

Theorem gateway_thread_with_reference_history {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects
    (contract : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    decimal_float ledger retired held
    (runtime : gateway_thread_runtime backend io native stable base thread_errno) :
  gateway_thread_runtime backend io native stable
    (gateway_thread_invariant_discipline base
      (gateway_reference_history_scope python objects decimal_float ledger retired held)) thread_errno.
Proof.
  apply gateway_thread_with_invariant with (heap_allocation := heap_allocation);
    [exact runtime |apply gateway_reference_history_thread_invariant; exact contract].
Qed.
