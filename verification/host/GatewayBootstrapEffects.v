(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Retain only the actual input spans outside one primitive's writes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayBootstrapRuntime GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_protected_effect {World} native stable output before world after next
    object offset bytes :
  @gateway_bootstrap_protected World native stable before world (Vptr object offset) bytes ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable output world before after ->
  (forall position, Ptrofs.unsigned offset <= position <
    Ptrofs.unsigned offset + Z.of_nat (length bytes) -> ~ output object position) ->
  gateway_bootstrap_protected native stable after next (Vptr object offset) bytes.
Proof.
  intros [actual [actual_offset [POINTER [[loaded [loaded_offset [LOCATION [BOUND LOAD]]]] OWNED]]]]
    ACCESS FRAME OUTSIDE.
  inversion POINTER; subst actual actual_offset.
  inversion LOCATION; subst loaded loaded_offset.
  exists object, offset; split; [reflexivity |]. split.
  - exists object, offset; split; [reflexivity |]. split; [exact BOUND |].
    eapply Mem.loadbytes_unchanged_on; [exact FRAME | |exact LOAD].
    intros position RANGE; split; [apply OWNED; exact RANGE |apply OUTSIDE; exact RANGE].
  - intros position RANGE.
    assert (READABLE : Mem.perm before object position Cur Readable) by
      (eapply Mem.loadbytes_range_perm; [exact LOAD |exact RANGE]).
    destruct (OWNED position RANGE) as [PRIVATE |STABLE].
    + left; eapply (proj1 ACCESS);
        [eapply Mem.perm_valid_block; exact READABLE |exact PRIVATE].
    + right; eapply (proj2 ACCESS); eassumption.
Qed.

Theorem gateway_bootstrap_owned_cstring {World} (native : World -> block -> Prop) stable
    memory world object offset bytes :
  native world object -> gateway_error_cstring memory (Vptr object offset) bytes ->
  gateway_bootstrap_protected native stable memory world (Vptr object offset) (bytes ++ [Byte.zero]).
Proof.
  intros PRIVATE [actual [actual_offset [POINTER [NONZERO [BOUND LOAD]]]]].
  inversion POINTER; subst actual actual_offset.
  exists object, offset; split; [reflexivity |]. split.
  - exists object, offset; split; [reflexivity |]. split.
    + rewrite length_app, Nat2Z.inj_add; cbn; lia.
    + rewrite length_app, Nat2Z.inj_add; cbn; exact LOAD.
  - intros; left; exact PRIVATE.
Qed.
