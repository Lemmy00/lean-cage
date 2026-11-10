(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual suffix copying preserves the prefix and constructs the exact path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapMemory GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_append_copy {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    before world destination offset prefix source source_offset suffix returned after next observed :
  discipline None before world -> native world destination -> destination <> source ->
  ~ In Byte.zero prefix -> ~ In Byte.zero suffix ->
  Ptrofs.unsigned offset + Z.of_nat (length prefix) + Z.of_nat (length suffix) + 1 <= Ptrofs.modulus ->
  Z.of_nat (length (suffix ++ [Byte.zero])) <= Int64.max_unsigned ->
  gateway_bootstrap_bytes before (Vptr destination offset) prefix ->
  gateway_native_pointer before destination
    (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length prefix))))
    (Z.of_nat (length (suffix ++ [Byte.zero]))) Writable ->
  gateway_bootstrap_protected native stable before world (Vptr source source_offset) (suffix ++ [Byte.zero]) ->
  gateway_bootstrap_operation backend gateway_memory_copy_api
    [Vptr destination (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length prefix)))); Vptr source source_offset;
     Vlong (Int64.repr (Z.of_nat (length (suffix ++ [Byte.zero]))))]
    before world returned after next observed ->
  discipline None after next /\ native next destination /\
    gateway_error_cstring after (Vptr destination offset) (prefix ++ suffix).
Proof.
  intros SIDE PRIVATE SEPARATE PREFIX_NONZERO SUFFIX_NONZERO TOTAL COUNT PREFIX OWNED SOURCE OPERATION.
  set (shifted := Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length prefix)))).
  assert (SHIFT : Ptrofs.unsigned shifted = Ptrofs.unsigned offset + Z.of_nat (length prefix)).
  { unfold shifted; pose proof (Ptrofs.unsigned_range offset) as OFFSET.
    rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr (Z.of_nat (length prefix))) by
      (unfold Ptrofs.max_unsigned; lia).
    apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia. }
  destruct (@gateway_memory_copy_operation World Event backend io native stable discipline module_filename canonicalizes
    runtime before world destination shifted source source_offset (suffix ++ [Byte.zero])
    returned after next observed SIDE PRIVATE OWNED SOURCE (or_introl SEPARATE) COUNT OPERATION)
    as [[NEXT [ACCESS [FRAME QUIET]]] [PERMISSIONS [RESULT COPIED]]].
  split; [exact NEXT |]. split.
  - apply (proj1 ACCESS destination); [exact (proj1 (proj2 (proj2 OWNED))) |exact PRIVATE].
  - assert (PREFIX_AFTER : gateway_bootstrap_bytes after (Vptr destination offset) prefix).
    { eapply gateway_bootstrap_bytes_unchanged; [exact PREFIX |].
      eapply Mem.unchanged_on_implies; [exact FRAME |].
      intros object position [SAME INSIDE]; subst object; split; [left; exact PRIVATE |].
      intros [SAME WRITE].
      change (Ptrofs.unsigned shifted <= position <
        Ptrofs.unsigned shifted + Z.of_nat (length (suffix ++ [Byte.zero]))) in WRITE.
      rewrite SHIFT in WRITE; lia. }
    apply gateway_bootstrap_cstring_from_bytes.
    + intro ZERO; apply in_app_or in ZERO; destruct ZERO; contradiction.
    + replace ((prefix ++ suffix) ++ [Byte.zero]) with (prefix ++ (suffix ++ [Byte.zero])) by
        (rewrite app_assoc; reflexivity).
      eapply gateway_bootstrap_bytes_concat; [lia | |exact PREFIX_AFTER |exact COPIED].
      rewrite length_app, Nat2Z.inj_add; cbn; lia.
Qed.
