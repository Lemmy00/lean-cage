(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual bounded C length tests justify subtraction and every copied extent. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Ctypes Cop Clight.
From HostGateway Require Import GatewayBootstrapConstants.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_bootstrap_length_guard length :
  0 <= length ->
  Int64.cmpu Cgt (Int64.repr (Z.min 4096 length)) (Int64.repr 4095) = false ->
  length <= 4095 /\ Z.min 4096 length = length.
Proof.
  intros NONNEGATIVE CHECK.
  assert (RANGE : 0 <= Z.min 4096 length <= 4096) by lia.
  unfold Int64.cmpu, Int64.ltu in CHECK.
  rewrite !Int64.unsigned_repr in CHECK by
    (change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (zlt 4095 (Z.min 4096 length)); [discriminate |].
  destruct (Z.min_spec 4096 length) as [[ORDER MIN] |[ORDER MIN]]; split; lia.
Qed.

Lemma gateway_bootstrap_tail_guard length :
  0 <= length <= 4095 ->
  Int64.cmpu Cle (Int64.repr length) (Int64.repr 30) = false -> 30 < length.
Proof.
  intros RANGE CHECK; unfold Int64.cmpu, Int64.ltu in CHECK.
  rewrite !Int64.unsigned_repr in CHECK by
    (change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (zlt 30 length); cbn in CHECK; [exact l |discriminate].
Qed.

Theorem gateway_bootstrap_copy_geometry loaded_size canonical_size :
  30 < loaded_size <= 4095 -> 30 < canonical_size <= 4095 ->
  let api_size := loaded_size - 30 in let root_size := canonical_size - 30 in
  0 < api_size /\ 0 < root_size /\
  root_size + Z.of_nat (length bootstrap_executable_bytes) + 1 <= 4096 /\
  api_size + Z.of_nat (length bootstrap_results_bytes) + 1 <= 4096 /\
  Int64.sub (Int64.repr loaded_size) (Int64.repr 30) = Int64.repr api_size /\
  Int64.sub (Int64.repr canonical_size) (Int64.repr 30) = Int64.repr root_size /\
  Int64.unsigned (Int64.add (Int64.repr root_size) (Int64.repr 19)) = root_size + 19 /\
  Int64.unsigned (Int64.add (Int64.repr api_size) (Int64.repr 21)) = api_size + 21.
Proof.
  intros LOADED CANONICAL; cbn zeta.
  assert (API : 0 < loaded_size - 30 <= 4065) by lia.
  assert (ROOT : 0 < canonical_size - 30 <= 4065) by lia.
  repeat split; try (cbn; lia).
  - unfold Int64.sub; rewrite !Int64.unsigned_repr by
      (change Int64.max_unsigned with 18446744073709551615; lia); reflexivity.
  - unfold Int64.sub; rewrite !Int64.unsigned_repr by
      (change Int64.max_unsigned with 18446744073709551615; lia); reflexivity.
  - unfold Int64.add.
    rewrite (Int64.unsigned_repr (canonical_size - 30)) by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    change (Int64.unsigned (Int64.repr (canonical_size - 30 + 19)) = canonical_size - 30 + 19).
    apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615; lia.
  - unfold Int64.add.
    rewrite (Int64.unsigned_repr (loaded_size - 30)) by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    change (Int64.unsigned (Int64.repr (loaded_size - 30 + 21)) = loaded_size - 30 + 21).
    apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615; lia.
Qed.
