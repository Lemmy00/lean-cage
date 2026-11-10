(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual memcpy copies exactly the checked filename prefix. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapSlice GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_prefix_copy {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    before world destination destination_offset source source_offset bytes count returned after next observed :
  discipline None before world -> native world destination -> destination <> source ->
  (count <= length bytes)%nat -> Z.of_nat count <= Int64.max_unsigned ->
  gateway_native_pointer before destination destination_offset (Z.of_nat count) Writable ->
  gateway_bootstrap_protected native stable before world (Vptr source source_offset) (bytes ++ [Byte.zero]) ->
  gateway_bootstrap_operation backend gateway_memory_copy_api
    [Vptr destination destination_offset; Vptr source source_offset; Vlong (Int64.repr (Z.of_nat count))]
    before world returned after next observed ->
  gateway_bootstrap_post io native stable discipline
    (gateway_native_region destination destination_offset (Z.of_nat count)) before world after next observed /\
  gateway_native_permissions before after destination destination_offset (Z.of_nat count) /\
  returned = Vptr destination destination_offset /\
  gateway_bootstrap_bytes after (Vptr destination destination_offset) (firstn count bytes).
Proof.
  intros SIDE PRIVATE SEPARATE COUNT WIDTH WRITABLE SOURCE OPERATION.
  pose proof (gateway_bootstrap_protected_slice native stable before world source source_offset
    (bytes ++ [Byte.zero]) 0 count SOURCE
    ltac:(rewrite length_app; cbn; lia) ltac:(rewrite length_app; cbn; lia)) as PREFIX.
  rewrite skipn_O, Ptrofs.add_zero in PREFIX.
  rewrite firstn_app in PREFIX.
  replace (count - length bytes)%nat with O in PREFIX by lia.
  rewrite firstn_O, app_nil_r in PREFIX.
  assert (LENGTH : length (firstn count bytes) = count) by (rewrite firstn_length; lia).
  pose proof (@gateway_memory_copy_operation World Event backend io native stable discipline module_filename canonicalizes
    runtime before world destination destination_offset source source_offset (firstn count bytes)
    returned after next observed) as COPY.
  rewrite LENGTH in COPY.
  apply COPY; [exact SIDE |exact PRIVATE |exact WRITABLE |exact PREFIX |
    left; exact SEPARATE |exact WIDTH |exact OPERATION].
Qed.
