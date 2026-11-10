(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Equivalent source allocation identities share the same pointer and byte scopes. *)
From Stdlib Require Import List.
From compcert Require Import Maps Values Memory Memdata.
From HostGateway Require Import GatewayPointerOrigins GatewayPointerMemory GatewayRuntimeMemory.

Lemma gateway_pointer_avoids_equivalent (first second : block -> Prop) value :
  (forall object, first object <-> second object) ->
  (gateway_pointer_avoids first value <-> gateway_pointer_avoids second value).
Proof. intro SAME; destruct value; cbn [gateway_pointer_avoids]; try tauto; specialize (SAME b); tauto. Qed.

Lemma gateway_memory_avoids_equivalent (first second : block -> Prop) memory :
  (forall object, first object <-> second object) ->
  gateway_memory_avoids first memory -> gateway_memory_avoids second memory.
Proof.
  intros SAME AVOIDS object offset; specialize (AVOIDS object offset).
  unfold gateway_memval_avoids in *; destruct (ZMap.get offset (PMap.get object (Mem.mem_contents memory)));
    try exact I; apply (proj1 (gateway_pointer_avoids_equivalent first second _ SAME)); exact AVOIDS.
Qed.

Theorem gateway_runtime_scope_equivalent (first second : block -> Prop) memory pool :
  (forall object, first object <-> second object) ->
  gateway_runtime_memory_scope first memory pool -> gateway_runtime_memory_scope second memory pool.
Proof.
  intros SAME [MEMORY [LIVE POOL]]; split.
  - eapply gateway_memory_avoids_equivalent; eassumption.
  - split.
    + intros object PRIVATE; apply LIVE, (proj2 (SAME object)); exact PRIVATE.
    + eapply Forall_impl; [|exact POOL]. intros value AVOIDS.
      exact (proj1 (gateway_pointer_avoids_equivalent first second value SAME) AVOIDS).
Qed.

Theorem gateway_callback_origin_equivalent (first second : block -> Prop) guard callback :
  (forall object, first object <-> second object) ->
  gateway_callback_memory_origin first guard callback -> gateway_callback_memory_origin second guard callback.
Proof.
  intros SAME CALLBACK before arguments after result MEMORY LIVE ARGUMENTS RUN.
  assert (INPUT : gateway_runtime_memory_scope first before arguments).
  { eapply gateway_runtime_scope_equivalent; [intro object; symmetry; apply SAME |].
    exact (conj MEMORY (conj LIVE ARGUMENTS)). }
  destruct INPUT as [MEMORY0 [LIVE0 ARGUMENTS0]].
  destruct (CALLBACK before arguments after result MEMORY0 LIVE0 ARGUMENTS0 RUN)
    as [FINAL [RETAINED [RESULT FRAME]]].
  split; [eapply gateway_memory_avoids_equivalent; eassumption |split].
  - intros object PRIVATE; apply RETAINED, (proj2 (SAME object)); exact PRIVATE.
  - split; [apply (proj1 (gateway_pointer_avoids_equivalent first second result SAME)); exact RESULT |].
    intro ACTIVE; eapply Mem.unchanged_on_implies; [apply FRAME; exact ACTIVE |].
    intros object offset PRIVATE VALID; apply (proj2 (SAME object)); exact PRIVATE.
Qed.
