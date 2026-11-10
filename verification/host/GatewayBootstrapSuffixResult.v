(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual comparison result decides equality of the received filename suffix. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapSlice GatewayBootstrapConstants GatewayBootstrapRetention GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_bootstrap_suffix_result {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    ge before world object offset bytes suffix continuation returned after next observed :
  discipline None before world ->
  gateway_bootstrap_protected native stable before world (Vptr object offset) (bytes ++ [Byte.zero]) ->
  (30 < length bytes)%nat ->
  gateway_bootstrap_protected native stable before world (Vptr suffix Ptrofs.zero)
    (bootstrap_suffix_bytes ++ [Byte.zero]) ->
  gateway_step backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_memory_compare_api)
      [Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes) - 30)));
       Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)] continuation before) world)
    (gateway_primitive observed)
    (gateway_live (Returnstate returned continuation after) next) ->
  gateway_bootstrap_post io native stable discipline gateway_native_no_output before world after next observed /\
  exists status, returned = Vint status /\
    (status = Int.zero <-> skipn (length bytes - 30) bytes = bootstrap_suffix_bytes).
Proof.
  intros SIDE PROTECTED LONG SUFFIX STEP.
  pose proof (gateway_bootstrap_filename_suffix native stable before world object offset bytes PROTECTED LONG)
    as LEFT.
  assert (COUNT : length (skipn (length bytes - 30) bytes) = 30%nat) by
    (rewrite skipn_length; lia).
  assert (SHIFT : Z.of_nat (length bytes - 30) = Z.of_nat (length bytes) - 30) by
    (rewrite Nat2Z.inj_sub by lia; reflexivity).
  rewrite SHIFT in LEFT.
  pose proof (gateway_bootstrap_protected_slice native stable before world suffix Ptrofs.zero
    (bootstrap_suffix_bytes ++ [Byte.zero]) 0 30 SUFFIX ltac:(cbn; lia) ltac:(cbn; lia)) as RIGHT.
  change (gateway_bootstrap_protected native stable before world (Vptr suffix Ptrofs.zero)
    bootstrap_suffix_bytes) in RIGHT.
  assert (OPERATION : gateway_bootstrap_operation backend gateway_memory_compare_api
    [Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes) - 30)));
     Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)] before world returned after next observed).
  { inversion STEP; subst;
      cbn [gateway_bootstrap_operation gateway_bootstrap_signature gateway_runtime_operation]; eassumption. }
  assert (EXACT_COUNT : Vlong (Int64.repr 30) =
    Vlong (Int64.repr (Z.of_nat (length (skipn (length bytes - 30) bytes))))).
  { rewrite COUNT; reflexivity. }
  rewrite EXACT_COUNT in OPERATION.
  eapply gateway_memory_compare_operation;
    [exact runtime |exact SIDE |exact LEFT |exact RIGHT |rewrite COUNT; reflexivity |
     rewrite COUNT; change (30 <= 18446744073709551615); lia |exact OPERATION].
Qed.
