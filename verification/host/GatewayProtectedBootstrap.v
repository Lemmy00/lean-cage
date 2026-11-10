(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual loader/string frames preserve protected descriptors. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayProtectedMemory
  GatewayProtectedThreads GatewayBootstrapRuntime GatewayBootstrapABI.
Open Scope Z_scope.

Theorem gateway_bootstrap_protected_widen {World} native stable protected immutable memory world pointer bytes :
  @gateway_bootstrap_protected World (gateway_protected_native native protected immutable) stable memory world pointer bytes ->
  gateway_bootstrap_protected native stable memory world pointer bytes.
Proof.
  intros [object [offset [POINTER [BYTES OWNED]]]].
  exists object, offset; split; [exact POINTER |]. split; [exact BYTES |].
  intros position RANGE; destruct (OWNED position RANGE) as [PRIVATE |READONLY];
    [left; exact (proj1 PRIVATE) |right; exact READONLY].
Qed.

Section ProtectedBootstrap.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline module_filename canonicalizes
  (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
  (protected immutable : block -> Prop) (snapshot : mem).
Let restricted := gateway_protected_native native protected immutable.
Let side := gateway_protected_discipline discipline native protected immutable snapshot.

Local Lemma protected_quiet before world after next observed :
  side None before world -> gateway_bootstrap_post io native stable discipline gateway_native_no_output
    before world after next observed ->
  gateway_bootstrap_post io restricted stable side gateway_native_no_output before world after next observed.
Proof.
  intros [SIDE STATE] [NEXT [ACCESS [FRAME QUIET]]]; split.
  - split; [exact NEXT |]. eapply gateway_protected_effect;
      [exact STATE |exact ACCESS |exact FRAME |intros; unfold gateway_native_no_output; tauto].
  - split; [apply gateway_protected_access; exact ACCESS |].
    split; [apply gateway_protected_frame; exact FRAME |exact QUIET].
Qed.

Local Lemma protected_written before world after next observed object offset amount :
  side None before world -> restricted world object -> gateway_native_pointer before object offset amount Writable ->
  gateway_bootstrap_post io native stable discipline (gateway_native_region object offset amount)
    before world after next observed ->
  gateway_bootstrap_post io restricted stable side (gateway_native_region object offset amount)
    before world after next observed.
Proof.
  intros [SIDE STATE] OWNED POINTER [NEXT [ACCESS [FRAME QUIET]]]; split.
  - split; [exact NEXT |]. eapply gateway_protected_effect;
      [exact STATE |exact ACCESS |exact FRAME |].
    intros candidate position GUARDED [SAME RANGE]; subst candidate.
    eapply gateway_protected_writable_separate; [exact STATE |exact OWNED | |exact GUARDED].
    exact ((proj2 (proj2 (proj2 POINTER))) position RANGE).
  - split; [apply gateway_protected_access; exact ACCESS |].
    split; [apply gateway_protected_frame; exact FRAME |exact QUIET].
Qed.

Theorem gateway_protected_bootstrap :
  gateway_bootstrap_runtime backend io restricted stable side module_filename canonicalizes.
Proof.
  constructor.
  - intros before world address object offset result after next observed SIDE OWNED POINTER ACCESS OPERATION.
    destruct (gateway_loader_address_operation _ _ _ _ _ _ _ runtime before world address object offset result after next observed
      (proj1 SIDE) (proj1 OWNED) POINTER ACCESS OPERATION) as [POST [PERMISSIONS RESULT]].
    split; [eapply protected_written; eassumption |]. split; [exact PERMISSIONS |].
    destruct RESULT as [status [VALUE SUCCESS]]; exists status; split; [exact VALUE |].
    intro NONZERO; destruct (SUCCESS NONZERO) as [filename [LOAD NAME]]; exists filename; split; [exact LOAD |].
    destruct NAME as [NULL |[bytes [name [name_offset [POINTER_VALUE [STRING [REGION [FOREIGN PROVENANCE]]]]]]]];
      [left; exact NULL |right].
    exists bytes, name, name_offset; split; [exact POINTER_VALUE |]. split; [exact STRING |]. split.
    + destruct REGION as [actual [actual_offset [LOCATION [BYTES READONLY]]]].
      exists actual, actual_offset; split; [exact LOCATION |]. split; [exact BYTES |].
      intros position RANGE; destruct (READONLY position RANGE) as [PRIVATE |STABLE].
      * left; split; [exact PRIVATE |]. intro GUARDED.
        rewrite POINTER_VALUE in LOCATION; inversion LOCATION; subst actual actual_offset; contradiction.
      * right; exact STABLE.
    + split; [intro PRIVATE; apply FOREIGN; exact (proj1 PRIVATE) |exact PROVENANCE].
  - intros before world pointer bytes maximum result after next observed SIDE STRING REGION BOUND OPERATION.
    destruct (gateway_bounded_length_operation _ _ _ _ _ _ _ runtime before world pointer bytes maximum result after next observed
      (proj1 SIDE) STRING (gateway_bootstrap_protected_widen native stable protected immutable before world pointer
        (bytes ++ Byte.zero :: nil) REGION) BOUND OPERATION) as [POST RESULT].
    split; [eapply protected_quiet; eassumption |exact RESULT].
  - intros before world first second left right result after next observed SIDE FIRST SECOND SIZE BOUND OPERATION.
    destruct (gateway_memory_compare_operation _ _ _ _ _ _ _ runtime before world first second left right result after next observed
      (proj1 SIDE) (gateway_bootstrap_protected_widen native stable protected immutable before world first left FIRST)
      (gateway_bootstrap_protected_widen native stable protected immutable before world second right SECOND)
      SIZE BOUND OPERATION) as [POST RESULT].
    split; [eapply protected_quiet; eassumption |exact RESULT].
  - intros before world destination destination_offset source source_offset bytes result after next observed
      SIDE OWNED POINTER REGION DISJOINT BOUND OPERATION.
    destruct (gateway_memory_copy_operation _ _ _ _ _ _ _ runtime before world destination destination_offset source source_offset
      bytes result after next observed (proj1 SIDE) (proj1 OWNED) POINTER
      (gateway_bootstrap_protected_widen native stable protected immutable before world (Vptr source source_offset) bytes REGION)
      DISJOINT BOUND OPERATION) as [POST [PERMISSIONS [RESULT BYTES]]].
    split; [eapply protected_written; eassumption |].
    split; [exact PERMISSIONS |]. split; assumption.
  - intros before world pointer original destination result after next observed SIDE STRING REGION OWNED POINTER DISJOINT OPERATION.
    destruct (gateway_canonical_path_operation _ _ _ _ _ _ _ runtime before world pointer original destination result after next observed
      (proj1 SIDE) STRING
      (gateway_bootstrap_protected_widen native stable protected immutable before world pointer (original ++ Byte.zero :: nil) REGION)
      (proj1 OWNED) POINTER DISJOINT OPERATION) as [POST [PERMISSIONS RESULT]].
    split; [eapply protected_written; eassumption |]. split; assumption.
Qed.
End ProtectedBootstrap.
