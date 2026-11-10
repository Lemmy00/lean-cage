(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Checked names produce exactly the actual copy inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayBootstrapRegions GatewayBootstrapBuffers GatewayBootstrapRuntime
  GatewayBootstrapCheckContext GatewayBootstrapCanonicalResult GatewayBootstrapInformation
  GatewayBootstrapPathContext GatewayBootstrapCopyState GatewayBootstrapSpans GatewayBootstrapSlice
  GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_path_prefix (bytes : list Byte.int) := firstn (length bytes - 30) bytes.

Theorem bootstrap_path_prefix_extent bytes :
  30 < Z.of_nat (length bytes) <= 4095 ->
  Z.of_nat (length (bootstrap_path_prefix bytes)) = Z.of_nat (length bytes) - 30 /\
  0 < Z.of_nat (length (bootstrap_path_prefix bytes)) <= 4065.
Proof.
  intro LENGTH; unfold bootstrap_path_prefix; rewrite firstn_length, Nat.min_l by lia.
  rewrite Nat2Z.inj_sub by lia; cbn; lia.
Qed.

Theorem bootstrap_path_prefix_no_zero bytes :
  ~ In Byte.zero bytes -> ~ In Byte.zero (bootstrap_path_prefix bytes).
Proof.
  intros NONZERO ZERO; apply NONZERO.
  unfold bootstrap_path_prefix in ZERO; rewrite <- (firstn_skipn (length bytes - 30) bytes).
  apply in_or_app; left; exact ZERO.
Qed.

Theorem bootstrap_path_prefix_nonzero memory object offset bytes :
  gateway_error_cstring memory (Vptr object offset) bytes -> ~ In Byte.zero (bootstrap_path_prefix bytes).
Proof.
  intros [actual [actual_offset [POINTER [NONZERO _]]]] ZERO; apply NONZERO.
  unfold bootstrap_path_prefix in ZERO; rewrite <- (firstn_skipn (length bytes - 30) bytes).
  apply in_or_app; left; exact ZERO.
Qed.

Theorem bootstrap_path_prefix_protected {World} native stable memory (world : World) object offset bytes :
  gateway_bootstrap_protected native stable memory world (Vptr object offset) (bytes ++ [Byte.zero]) ->
  gateway_bootstrap_protected native stable memory world (Vptr object offset) (bootstrap_path_prefix bytes).
Proof.
  intro SOURCE.
  pose proof (gateway_bootstrap_protected_slice native stable memory world object offset
    (bytes ++ [Byte.zero]) 0 (length bytes - 30) SOURCE
    ltac:(rewrite length_app; cbn; lia) ltac:(rewrite length_app; cbn; lia)) as PREFIX.
  rewrite skipn_O, Ptrofs.add_zero, firstn_app in PREFIX.
  replace (length bytes - 30 - length bytes)%nat with O in PREFIX by lia.
  rewrite firstn_O, app_nil_r in PREFIX; exact PREFIX.
Qed.

Theorem actual_bootstrap_checked_copy_context {World} native stable discipline
    information resolved filename filename_offset root engine results suffix executable results_literal
    original canonical memory (world : World) :
  gateway_bootstrap_check_context native stable discipline
    ((information, 32, Freeable) :: (resolved, 4096, Freeable) ::
      bootstrap_loaded_capacities root engine results suffix executable results_literal)
    (bootstrap_loaded_literals suffix executable results_literal)
    information filename filename_offset original resolved canonical memory world ->
  gateway_bootstrap_path_context native stable discipline
    (bootstrap_copy_buffers information resolved root engine results) information (Vptr filename filename_offset)
    (bootstrap_copy_spans 0 resolved filename filename_offset root engine results executable results_literal
      (bootstrap_path_prefix canonical) (bootstrap_path_prefix original)) memory world.
Proof.
  intros [[SIDE [CAPACITIES LITERALS]] [INPUT [PRIVATE [WRITABLE [STRING PROTECTED]]]]].
  split.
  - split; [exact SIDE |]. split.
    + intros object amount access MEMBER; apply CAPACITIES.
      unfold bootstrap_copy_buffers in MEMBER; unfold bootstrap_loaded_capacities; cbn [In] in *; tauto.
    + intros object bytes MEMBER; inversion MEMBER.
  - split; [exact (proj1 INPUT) |].
    intros object offset bytes MEMBER; cbn [bootstrap_copy_spans In] in MEMBER.
    repeat destruct MEMBER as [SAME |MEMBER]; try contradiction;
      inversion SAME; subst object offset bytes.
    + apply bootstrap_path_prefix_protected; exact PROTECTED.
    + apply bootstrap_path_prefix_protected; exact (proj2 (proj2 INPUT)).
    + apply LITERALS; unfold bootstrap_loaded_literals; cbn [In]; auto.
    + apply LITERALS; unfold bootstrap_loaded_literals; cbn [In]; auto.
Qed.
