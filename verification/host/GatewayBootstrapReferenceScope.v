(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Compose actual libc effects with the current active and archived reference pool. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Floats.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayThreadRuntime GatewayThreadInvariant
  GatewayBootstrapABI GatewayBootstrapRuntime GatewayBootstrapPython GatewayBootstrapReference
  GatewayReferenceHistoryThreads GatewayReferenceThreads GatewayReferenceAccounting GatewayReferenceAbandon
  GatewayReferenceLedger GatewayReferenceHistory GatewayObjectThreads GatewayReferenceHeld.
Import ListNotations.
Open Scope Z_scope.

(* Memory/runtime representation: a held, clear interpreter is ready; native
   output buffers belong outside its actual managed allocation blocks. *)
Record gateway_bootstrap_python_profile {World} (native : World -> block -> Prop)
    (base : option Values.val -> mem -> World -> Prop)
    (python : World -> python_world) (objects : World -> gateway_object_heap) : Prop := {
  gateway_bootstrap_profile_ready : forall memory world, base None memory world ->
    gateway_objects_ready (python world) (objects world) memory;
  gateway_bootstrap_profile_native : forall memory world object, base None memory world ->
    native world object -> ~ python_runtime_owned (python world) object
}.

Theorem gateway_bootstrap_protected_bytes {World} native stable memory world pointer bytes :
  @gateway_bootstrap_protected World native stable memory world pointer bytes ->
  gateway_bootstrap_bytes memory pointer bytes.
Proof. intros [object [offset [POINTER [BYTES OWNED]]]]; exact BYTES. Qed.

Section ReferenceScope.
Context {World Event} (backend : gateway_backend World Event) io native stable base module_filename canonicalizes
  (runtime : gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
  python objects
  (profile : gateway_bootstrap_python_profile native base python objects)
  (references : gateway_bootstrap_reference_runtime backend python objects)
  (decimal_float : list Z -> Floats.float -> Prop) (ledger : gateway_reference_ledger)
  (retired : list gateway_abandoned_reference) (held : list gateway_held_value).
Let property := gateway_reference_history_scope python objects decimal_float ledger retired held.
Let side := gateway_thread_invariant_discipline base property.

Local Lemma reference_post api arguments before world result after next observed output :
  side None before world ->
  gateway_bootstrap_python_outputs (python world) api arguments ->
  gateway_bootstrap_arguments_valid before api arguments ->
  gateway_bootstrap_operation backend api arguments before world result after next observed ->
  gateway_bootstrap_post io native stable base output before world after next observed ->
  gateway_bootstrap_post io native stable side output before world after next observed.
Proof.
  intros [SIDE HISTORY] OUTPUTS VALID OPERATION [NEXT REST].
  destruct (gateway_bootstrap_reference_operation _ _ _ references api arguments before world result after next observed
    (gateway_bootstrap_profile_ready _ _ _ _ profile before world SIDE) OUTPUTS VALID OPERATION)
    as [PYTHON [OBJECTS FRAME]].
  split; [|exact REST]. split; [exact NEXT |].
  unfold property, gateway_reference_history_scope, gateway_reference_scope,
    gateway_reference_held in HISTORY |- *.
  rewrite PYTHON, OBJECTS; exact HISTORY.
Qed.

Theorem gateway_bootstrap_with_reference_history :
  gateway_bootstrap_runtime backend io native stable side module_filename canonicalizes.
Proof.
  constructor.
  - intros before world address object offset result after next observed SIDE OWNED POINTER ACCESS OPERATION.
    destruct (gateway_loader_address_operation _ _ _ _ _ _ _ runtime before world address object offset result after next observed
      (proj1 SIDE) OWNED POINTER ACCESS OPERATION) as [POST RESULT].
    split; [|exact RESULT].
    eapply reference_post with (api := gateway_loader_address_api) (arguments := [address; Vptr object offset]) (result := result);
      [exact SIDE | |split; assumption |exact OPERATION |exact POST].
    cbn; exact (gateway_bootstrap_profile_native native base python objects profile before world object (proj1 SIDE) OWNED).
  - intros before world pointer bytes maximum result after next observed SIDE STRING REGION BOUND OPERATION.
    destruct (gateway_bounded_length_operation _ _ _ _ _ _ _ runtime before world pointer bytes maximum result after next observed
      (proj1 SIDE) STRING REGION BOUND OPERATION) as [POST RESULT].
    split; [|exact RESULT].
    eapply reference_post with (api := gateway_bounded_length_api)
      (arguments := [pointer; Vlong (Int64.repr maximum)]) (result := result);
      [exact SIDE |exact I |exists bytes; exact STRING |exact OPERATION |exact POST].
  - intros before world first second left right result after next observed SIDE FIRST SECOND SIZE BOUND OPERATION.
    destruct (gateway_memory_compare_operation _ _ _ _ _ _ _ runtime before world first second left right result after next observed
      (proj1 SIDE) FIRST SECOND SIZE BOUND OPERATION) as [POST RESULT].
    split; [|exact RESULT].
    eapply reference_post with (api := gateway_memory_compare_api)
      (arguments := [first; second; Vlong (Int64.repr (Z.of_nat (length left)))]) (result := result);
      [exact SIDE |exact I | |exact OPERATION |exact POST].
    exists left, right; split.
    + rewrite Int64.unsigned_repr; [reflexivity |lia].
    + split; [exact SIZE |]. split; eapply gateway_bootstrap_protected_bytes; eassumption.
  - intros before world destination destination_offset source source_offset bytes result after next observed
      SIDE OWNED POINTER REGION DISJOINT BOUND OPERATION.
    destruct (gateway_memory_copy_operation _ _ _ _ _ _ _ runtime before world destination destination_offset source source_offset bytes
      result after next observed (proj1 SIDE) OWNED POINTER REGION DISJOINT BOUND OPERATION) as [POST RESULT].
    split; [|exact RESULT].
    eapply reference_post with (api := gateway_memory_copy_api)
      (arguments := [Vptr destination destination_offset; Vptr source source_offset;
        Vlong (Int64.repr (Z.of_nat (length bytes)))]) (result := result);
      [exact SIDE | | |exact OPERATION |exact POST].
    + cbn; exact (gateway_bootstrap_profile_native native base python objects profile before world destination (proj1 SIDE) OWNED).
    + exists bytes; rewrite Int64.unsigned_repr by lia.
      split; [reflexivity |]. split; [exact POINTER |]. split;
        [eapply gateway_bootstrap_protected_bytes; exact REGION |exact DISJOINT].
  - intros before world pointer original destination result after next observed SIDE STRING REGION OWNED POINTER DISJOINT OPERATION.
    destruct (gateway_canonical_path_operation _ _ _ _ _ _ _ runtime before world pointer original destination result after next observed
      (proj1 SIDE) STRING REGION OWNED POINTER DISJOINT OPERATION) as [POST RESULT].
    split; [|exact RESULT].
    eapply reference_post with (api := gateway_canonical_path_api)
      (arguments := [pointer; Vptr destination Ptrofs.zero]) (result := result);
      [exact SIDE | | |exact OPERATION |exact POST].
    + cbn; exact (gateway_bootstrap_profile_native native base python objects profile before world destination (proj1 SIDE) OWNED).
    + split; [exists original; exact STRING |]. split; assumption.
Qed.
End ReferenceScope.
