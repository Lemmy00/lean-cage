(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real zero-byte store terminates the retained copied root prefix. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayBootstrapRuntime GatewayBootstrapMemory GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_stored_terminator before after object offset bytes :
  gateway_bootstrap_bytes before (Vptr object offset) bytes -> ~ In Byte.zero bytes ->
  Ptrofs.unsigned offset + Z.of_nat (length bytes) + 1 <= Ptrofs.modulus ->
  Mem.store Mint8signed before object (Ptrofs.unsigned offset + Z.of_nat (length bytes))
    (Vint Int.zero) = Some after ->
  gateway_error_cstring after (Vptr object offset) bytes.
Proof.
  intros PREFIX NONZERO BOUND STORE.
  assert (SHIFT : Ptrofs.unsigned (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes)))) =
    Ptrofs.unsigned offset + Z.of_nat (length bytes)).
  { pose proof (Ptrofs.unsigned_range offset) as OFFSET.
    rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr (Z.of_nat (length bytes))) by
      (unfold Ptrofs.max_unsigned; lia).
    apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia. }
  assert (PREFIX_AFTER : gateway_bootstrap_bytes after (Vptr object offset) bytes).
  { eapply gateway_bootstrap_bytes_unchanged; [exact PREFIX |].
    eapply Mem.store_unchanged_on; [exact STORE |].
    intros position WRITE [SAME INSIDE]; cbn [size_chunk] in WRITE; lia. }
  assert (TERMINATOR : gateway_bootstrap_bytes after
    (Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes))))) [Byte.zero]).
  { exists object, (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes))));
      split; [reflexivity |]. split.
    - rewrite SHIFT; cbn; lia.
    - rewrite SHIFT; pose proof (Mem.loadbytes_store_same _ _ _ _ _ _ STORE) as LOADED.
      change (Mem.loadbytes after object (Ptrofs.unsigned offset + Z.of_nat (length bytes)) 1 =
        Some [Memdata.Byte Byte.zero]) in LOADED; exact LOADED. }
  eapply gateway_bootstrap_cstring_from_bytes; [exact NONZERO |].
  eapply gateway_bootstrap_bytes_concat; [lia |cbn; lia |exact PREFIX_AFTER |exact TERMINATOR].
Qed.
