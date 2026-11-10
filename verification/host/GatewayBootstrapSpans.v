(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A copy retains each actual disjoint span and adds only its written bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapBuffers GatewayBootstrapEffects GatewayBootstrapCapacities GatewayThreadRuntime GatewayFramedRuntime
  GatewayBootstrapMemory GatewayBootstrapSlice GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_spans {World} native stable
    (spans : list (block * ptrofs * list Byte.int)) memory (world : World) : Prop :=
  forall object offset bytes, In (object, offset, bytes) spans ->
    gateway_bootstrap_protected native stable memory world (Vptr object offset) bytes.

Theorem gateway_bootstrap_owned_bytes {World} native stable memory world object offset bytes :
  native world object -> gateway_bootstrap_bytes memory (Vptr object offset) bytes ->
  @gateway_bootstrap_protected World native stable memory world (Vptr object offset) bytes.
Proof.
  intros PRIVATE BYTES; exists object, offset; split; [reflexivity |].
  split; [exact BYTES |]. intros; left; exact PRIVATE.
Qed.

Theorem gateway_bootstrap_spans_effect {World} native stable before world after next spans retained output :
  @gateway_bootstrap_spans World native stable spans before world ->
  (forall span, In span retained -> In span spans) ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable output world before after ->
  (forall object offset bytes, In (object, offset, bytes) retained ->
    forall position, Ptrofs.unsigned offset <= position <
      Ptrofs.unsigned offset + Z.of_nat (length bytes) -> ~ output object position) ->
  gateway_bootstrap_spans native stable retained after next.
Proof.
  intros SPANS INCLUDED ACCESS FRAME OUTSIDE object offset bytes MEMBER.
  eapply gateway_bootstrap_protected_effect;
    [apply SPANS; apply INCLUDED; exact MEMBER |exact ACCESS |exact FRAME |apply OUTSIDE; exact MEMBER].
Qed.

Theorem gateway_bootstrap_spans_copy {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    before world after next spans retained destination destination_offset source source_offset bytes
    returned observed :
  discipline None before world -> native world destination ->
  gateway_native_pointer before destination destination_offset (Z.of_nat (length bytes)) Writable ->
  gateway_bootstrap_spans native stable spans before world ->
  In (source, source_offset, bytes) spans ->
  gateway_bootstrap_disjoint destination destination_offset (Z.of_nat (length bytes)) source source_offset ->
  Z.of_nat (length bytes) <= Int64.max_unsigned ->
  (forall span, In span retained -> In span spans) ->
  (forall object offset kept, In (object, offset, kept) retained ->
    forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length kept) ->
    ~ gateway_native_region destination destination_offset (Z.of_nat (length bytes)) object position) ->
  gateway_bootstrap_operation backend gateway_memory_copy_api
    [Vptr destination destination_offset; Vptr source source_offset;
     Vlong (Int64.repr (Z.of_nat (length bytes)))]
    before world returned after next observed ->
  gateway_bootstrap_post io native stable discipline
    (gateway_native_region destination destination_offset (Z.of_nat (length bytes))) before world after next observed /\
  gateway_native_permissions before after destination destination_offset (Z.of_nat (length bytes)) /\
  returned = Vptr destination destination_offset /\
  gateway_bootstrap_spans native stable ((destination, destination_offset, bytes) :: retained) after next.
Proof.
  intros SIDE PRIVATE POINTER SPANS SOURCE DISJOINT WIDTH INCLUDED OUTSIDE OPERATION.
  destruct (@gateway_memory_copy_operation World Event backend io native stable discipline module_filename canonicalizes
    runtime before world destination destination_offset source source_offset bytes returned after next observed
    SIDE PRIVATE POINTER (SPANS _ _ _ SOURCE) DISJOINT WIDTH OPERATION)
    as [POST [PERMISSIONS [VALUE BYTES]]].
  split; [exact POST |]. split; [exact PERMISSIONS |]. split; [exact VALUE |].
  intros object offset kept [SAME |MEMBER].
  - inversion SAME; subst object offset kept; eapply gateway_bootstrap_owned_bytes; [|exact BYTES].
    eapply (proj1 (proj1 (proj2 POST))); [exact (proj1 (proj2 (proj2 POINTER))) |exact PRIVATE].
  - eapply gateway_bootstrap_spans_effect;
      [exact SPANS |exact INCLUDED |exact (proj1 (proj2 POST)) |exact (proj1 (proj2 (proj2 POST))) |
       exact OUTSIDE |exact MEMBER].
Qed.

Theorem gateway_bootstrap_spans_cstring {World} native stable spans memory world object offset bytes :
  @gateway_bootstrap_spans World native stable spans memory world ->
  In (object, offset, bytes ++ [Byte.zero]) spans -> ~ In Byte.zero bytes ->
  gateway_error_cstring memory (Vptr object offset) bytes.
Proof.
  intros SPANS MEMBER NONZERO.
  destruct (SPANS _ _ _ MEMBER) as [actual [actual_offset [LOCATION [BYTES OWNED]]]].
  inversion LOCATION; subst actual actual_offset.
  eapply gateway_bootstrap_cstring_from_bytes; eassumption.
Qed.

Theorem gateway_bootstrap_spans_joined_cstring {World} native stable spans memory world object prefix suffix :
  @gateway_bootstrap_spans World native stable spans memory world ->
  In (object, Ptrofs.zero, prefix) spans ->
  In (object, Ptrofs.repr (Z.of_nat (length prefix)), suffix ++ [Byte.zero]) spans ->
  ~ In Byte.zero prefix -> ~ In Byte.zero suffix ->
  Z.of_nat (length prefix) + Z.of_nat (length suffix) + 1 <= Ptrofs.modulus ->
  gateway_error_cstring memory (Vptr object Ptrofs.zero) (prefix ++ suffix).
Proof.
  intros SPANS PREFIX SUFFIX PREFIX_NONZERO SUFFIX_NONZERO BOUND.
  destruct (SPANS _ _ _ PREFIX) as [first [first_offset [FIRST [FIRST_BYTES FIRST_OWNED]]]].
  inversion FIRST; subst first first_offset.
  destruct (SPANS _ _ _ SUFFIX) as [last [last_offset [LAST [LAST_BYTES LAST_OWNED]]]].
  inversion LAST; subst last last_offset.
  eapply gateway_bootstrap_cstring_from_bytes.
  - intro ZERO; apply in_app_or in ZERO; destruct ZERO; contradiction.
  - rewrite <- app_assoc.
    eapply gateway_bootstrap_bytes_concat.
    + change (0 + Z.of_nat (length prefix) < Ptrofs.modulus); lia.
    + rewrite length_app, Nat2Z.inj_add; cbn; change (0 + Z.of_nat (length prefix) + (Z.of_nat (length suffix) + 1) <= Ptrofs.modulus); lia.
    + exact FIRST_BYTES.
    + rewrite Ptrofs.add_zero_l; exact LAST_BYTES.
Qed.
