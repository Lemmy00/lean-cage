(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Native copies build exact bounded strings from initialized byte spans. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import WriteMemory.
From HostGateway Require Import GatewayBootstrapRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_cstring_from_bytes memory object offset bytes :
  ~ In Byte.zero bytes ->
  gateway_bootstrap_bytes memory (Vptr object offset) (bytes ++ [Byte.zero]) ->
  gateway_error_cstring memory (Vptr object offset) bytes.
Proof.
  intros NONZERO [actual [actual_offset [POINTER [BOUND LOAD]]]].
  inversion POINTER; subst actual actual_offset.
  exists object, offset; split; [reflexivity |]. split; [exact NONZERO |]. split.
  - rewrite length_app, Nat2Z.inj_add in BOUND; cbn in BOUND; lia.
  - rewrite length_app, Nat2Z.inj_add in LOAD; cbn in LOAD; exact LOAD.
Qed.

Theorem gateway_bootstrap_bytes_unchanged memory after object offset bytes :
  gateway_bootstrap_bytes memory (Vptr object offset) bytes ->
  Mem.unchanged_on (fun candidate position => candidate = object /\
    Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length bytes)) memory after ->
  gateway_bootstrap_bytes after (Vptr object offset) bytes.
Proof.
  intros [actual [actual_offset [POINTER [BOUND LOAD]]]] FRAME.
  inversion POINTER; subst actual actual_offset.
  exists object, offset; split; [reflexivity |]. split; [exact BOUND |].
  eapply Mem.loadbytes_unchanged_on; [exact FRAME | |exact LOAD].
  intros position RANGE; split; [reflexivity |exact RANGE].
Qed.

Theorem gateway_bootstrap_bytes_prefix memory object offset first rest :
  gateway_bootstrap_bytes memory (Vptr object offset) (first ++ rest) ->
  gateway_bootstrap_bytes memory (Vptr object offset) first.
Proof.
  intros [actual [actual_offset [POINTER [BOUND LOAD]]]].
  inversion POINTER; subst actual actual_offset.
  exists object, offset; split; [reflexivity |]. split.
  - rewrite length_app, Nat2Z.inj_add in BOUND; lia.
  - exact (load_first memory object (Ptrofs.unsigned offset) first rest LOAD).
Qed.

Theorem gateway_bootstrap_cstring_prefix memory object offset bytes count :
  gateway_error_cstring memory (Vptr object offset) bytes ->
  gateway_bootstrap_bytes memory (Vptr object offset) (firstn count bytes).
Proof.
  intros [actual [actual_offset [POINTER [NONZERO [BOUND LOAD]]]]].
  inversion POINTER; subst actual actual_offset.
  assert (FULL : gateway_bootstrap_bytes memory (Vptr object offset) (bytes ++ [Byte.zero])).
  { exists object, offset; split; [reflexivity |]. split.
    - rewrite length_app, Nat2Z.inj_add; cbn; lia.
    - rewrite length_app, Nat2Z.inj_add; cbn; exact LOAD. }
  rewrite <- (firstn_skipn count bytes), <- app_assoc in FULL.
  eapply gateway_bootstrap_bytes_prefix; exact FULL.
Qed.

Theorem gateway_bootstrap_bytes_concat memory object offset first rest :
  Ptrofs.unsigned offset + Z.of_nat (length first) < Ptrofs.modulus ->
  Ptrofs.unsigned offset + Z.of_nat (length first) + Z.of_nat (length rest) <= Ptrofs.modulus ->
  gateway_bootstrap_bytes memory (Vptr object offset) first ->
  gateway_bootstrap_bytes memory
    (Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length first))))) rest ->
  gateway_bootstrap_bytes memory (Vptr object offset) (first ++ rest).
Proof.
  intros INSIDE TOTAL [first_object [first_offset [FIRST [FIRST_BOUND FIRST_LOAD]]]]
    [rest_object [rest_offset [REST [REST_BOUND REST_LOAD]]]].
  inversion FIRST; subst first_object first_offset; inversion REST; subst rest_object rest_offset.
  assert (SHIFT : Ptrofs.unsigned (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length first)))) =
    Ptrofs.unsigned offset + Z.of_nat (length first)).
  { pose proof (Ptrofs.unsigned_range offset) as OFFSET.
    rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr (Z.of_nat (length first))) by
      (unfold Ptrofs.max_unsigned; lia).
    apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia. }
  rewrite SHIFT in REST_LOAD.
  exists object, offset; split; [reflexivity |]. split.
  - rewrite length_app, Nat2Z.inj_add; lia.
  - rewrite length_app, Nat2Z.inj_add, map_app.
    eapply Mem.loadbytes_concat; [exact FIRST_LOAD |exact REST_LOAD |lia |lia].
Qed.
