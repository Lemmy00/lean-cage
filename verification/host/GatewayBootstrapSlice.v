(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Suffix checks read the actual bounded filename slice. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import ScalarMemory.
From HostGateway Require Import GatewayBootstrapRuntime GatewayBootstrapMemory GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_bytes_slice memory object offset bytes start count :
  gateway_bootstrap_bytes memory (Vptr object offset) bytes ->
  (start + count <= length bytes)%nat ->
  (start < length bytes)%nat ->
  gateway_bootstrap_bytes memory
    (Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat start))))
    (firstn count (skipn start bytes)).
Proof.
  intros [actual [actual_offset [POINTER [BOUND LOAD]]]] RANGE START.
  inversion POINTER; subst actual actual_offset.
  assert (SHIFT : Ptrofs.unsigned (Ptrofs.add offset (Ptrofs.repr (Z.of_nat start))) =
    Ptrofs.unsigned offset + Z.of_nat start).
  { pose proof (Ptrofs.unsigned_range offset) as OFFSET.
    rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr (Z.of_nat start)) by
      (unfold Ptrofs.max_unsigned; lia).
    apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia. }
  assert (LENGTH : length (firstn count (skipn start bytes)) = count).
  { rewrite firstn_length, skipn_length; lia. }
  exists object, (Ptrofs.add offset (Ptrofs.repr (Z.of_nat start)));
    split; [reflexivity |]. split; [rewrite SHIFT, LENGTH; lia |].
  rewrite SHIFT, LENGTH.
  pose proof (loadbytes_slice memory object (Ptrofs.unsigned offset) (map Byte bytes)
    (Z.of_nat start) (Z.of_nat count)) as SLICE.
  rewrite map_length in SLICE.
  specialize (SLICE LOAD ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite !Nat2Z.id, skipn_map, firstn_map in SLICE; exact SLICE.
Qed.

Theorem gateway_bootstrap_protected_slice {World} native stable memory world object offset bytes start count :
  @gateway_bootstrap_protected World native stable memory world (Vptr object offset) bytes ->
  (start + count <= length bytes)%nat -> (start < length bytes)%nat ->
  gateway_bootstrap_protected native stable memory world
    (Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat start))))
    (firstn count (skipn start bytes)).
Proof.
  intros [actual [actual_offset [POINTER [BYTES OWNED]]]] RANGE START.
  inversion POINTER; subst actual actual_offset.
  pose proof (gateway_bootstrap_bytes_slice memory object offset bytes start count BYTES RANGE START) as SLICE.
  exists object, (Ptrofs.add offset (Ptrofs.repr (Z.of_nat start)));
    split; [reflexivity |]. split; [exact SLICE |].
  intros position INSIDE; apply OWNED.
  destruct BYTES as [actual [actual_offset [LOCATION [BOUND LOAD]]]];
    inversion LOCATION; subst actual actual_offset.
  assert (SHIFT : Ptrofs.unsigned (Ptrofs.add offset (Ptrofs.repr (Z.of_nat start))) =
    Ptrofs.unsigned offset + Z.of_nat start).
  { pose proof (Ptrofs.unsigned_range offset) as OFFSET.
    rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr (Z.of_nat start)) by
      (unfold Ptrofs.max_unsigned; lia).
    apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia. }
  rewrite SHIFT, firstn_length, skipn_length in INSIDE; lia.
Qed.

Theorem gateway_bootstrap_filename_suffix {World} native stable memory world object offset bytes :
  @gateway_bootstrap_protected World native stable memory world
    (Vptr object offset) (bytes ++ [Byte.zero]) ->
  (30 < length bytes)%nat ->
  gateway_bootstrap_protected native stable memory world
    (Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes - 30)))))
    (skipn (length bytes - 30) bytes).
Proof.
  intros PROTECTED LONG.
  pose proof (gateway_bootstrap_protected_slice native stable memory world object offset
    (bytes ++ [Byte.zero]) (length bytes - 30) 30 PROTECTED
    ltac:(rewrite length_app; cbn; lia) ltac:(rewrite length_app; cbn; lia)) as SUFFIX.
  assert (COUNT : length (skipn (length bytes - 30) bytes) = 30%nat) by
    (rewrite skipn_length; lia).
  rewrite skipn_app in SUFFIX.
  replace (length bytes - 30 - length bytes)%nat with O in SUFFIX by lia.
  rewrite skipn_O in SUFFIX.
  rewrite firstn_app, COUNT, Nat.sub_diag, firstn_all2, app_nil_r in SUFFIX by lia.
  exact SUFFIX.
Qed.
