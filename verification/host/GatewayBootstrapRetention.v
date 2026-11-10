(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual loader string remains readable through source checks. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayBootstrapRuntime GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_protected_retained {World} native stable before world after next pointer bytes :
  @gateway_bootstrap_protected World native stable before world pointer bytes ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_protected native stable after next pointer bytes.
Proof.
  intros [object [offset [POINTER [[actual [actual_offset [SAME [BOUND LOAD]]]] OWNED]]]] ACCESS FRAME.
  rewrite POINTER in SAME; inversion SAME; subst actual actual_offset.
  exists object, offset; split; [exact POINTER |]. split.
  - exists object, offset; split; [exact POINTER |]. split; [exact BOUND |].
    eapply Mem.loadbytes_unchanged_on; [exact FRAME | |exact LOAD].
    intros position RANGE; split; [apply OWNED; exact RANGE |cbn; tauto].
  - intros position RANGE.
    assert (READABLE : Mem.perm before object position Cur Readable).
    { eapply Mem.loadbytes_range_perm; [exact LOAD |exact RANGE]. }
    destruct (OWNED position RANGE) as [PRIVATE |STABLE].
    + left; eapply (proj1 ACCESS); [eapply Mem.perm_valid_block; exact READABLE |exact PRIVATE].
    + right; eapply (proj2 ACCESS); eassumption.
Qed.

Theorem gateway_bootstrap_cstring_retained {World} native stable before world after pointer bytes :
  gateway_error_cstring before pointer bytes ->
  @gateway_bootstrap_protected World native stable before world pointer (bytes ++ [Byte.zero]) ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_error_cstring after pointer bytes.
Proof.
  intros [object [offset [POINTER [NONZERO [BOUND LOAD]]]]]
    [actual [actual_offset [SAME [PROTECTED OWNED]]]] FRAME.
  rewrite POINTER in SAME; inversion SAME; subst actual actual_offset.
  exists object, offset; split; [exact POINTER |]. split; [exact NONZERO |]. split; [exact BOUND |].
  eapply Mem.loadbytes_unchanged_on; [exact FRAME | |exact LOAD].
  intros position RANGE; split; [apply OWNED |cbn; tauto].
  rewrite length_app, Nat2Z.inj_add; cbn; exact RANGE.
Qed.

Theorem gateway_bootstrap_cstring_pointer before object offset bytes :
  gateway_error_cstring before (Vptr object offset) bytes ->
  Mem.weak_valid_pointer before object (Ptrofs.unsigned offset) = true.
Proof.
  intros [actual [actual_offset [POINTER [NONZERO [BOUND LOAD]]]]]; inversion POINTER; subst actual actual_offset.
  apply Mem.valid_pointer_implies, Mem.valid_pointer_nonempty_perm.
  eapply Mem.perm_implies with (p1 := Readable); [|constructor].
  pose proof (Mem.loadbytes_range_perm _ _ _ _ _ LOAD) as READABLE.
  apply READABLE; lia.
Qed.
