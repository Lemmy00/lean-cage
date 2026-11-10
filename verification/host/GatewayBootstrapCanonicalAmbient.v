(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Interleaving retains the real canonical buffer and its full writable extent. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapRuntime GatewayBootstrapInformation
  GatewayBootstrapRetention GatewayBootstrapCanonicalResult GatewayThreadRuntime GatewayFramedRuntime.
Open Scope Z_scope.

Theorem gateway_bootstrap_native_pointer_frame {World} native stable before after world object offset amount :
  native world object -> 0 < amount ->
  gateway_native_pointer before object offset amount Writable ->
  @gateway_native_frame World native stable gateway_native_no_output world before after ->
  gateway_native_pointer after object offset amount Writable.
Proof.
  intros PRIVATE POSITIVE [NONNEGATIVE [BOUND [LIVE RANGE]]] FRAME.
  assert (KEEP : forall position,
    Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + amount ->
    Mem.perm after object position Cur Writable).
  { intros position INSIDE; eapply Mem.perm_unchanged_on;
      [exact FRAME |split; [left; exact PRIVATE |cbn; tauto] |apply RANGE; exact INSIDE]. }
  split; [exact NONNEGATIVE |]. split; [exact BOUND |]. split; [|exact KEEP].
  eapply Mem.perm_valid_block; apply (KEEP (Ptrofs.unsigned offset)); lia.
Qed.

Theorem gateway_bootstrap_canonical_retained {World} native stable discipline
    information object offset original resolved canonical before world after next :
  @gateway_bootstrap_canonical_information World native stable discipline
    information object offset original resolved canonical before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_canonical_information native stable discipline
    information object offset original resolved canonical after next.
Proof.
  intros [INFO [PRIVATE [WRITABLE [STRING PROTECTED]]]] SIDE ACCESS FRAME.
  split.
  - eapply gateway_bootstrap_filename_information_retained; eassumption.
  - split.
    + exact (proj1 ACCESS resolved (proj1 (proj2 (proj2 WRITABLE))) PRIVATE).
    + split.
      * eapply gateway_bootstrap_native_pointer_frame;
          [exact PRIVATE |lia |exact WRITABLE |exact FRAME].
      * split.
        -- eapply gateway_bootstrap_cstring_retained; eassumption.
        -- eapply gateway_bootstrap_protected_retained; eassumption.
Qed.

Theorem gateway_bootstrap_canonical_ambient {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    information object offset original resolved canonical :
  gateway_ambient_closed backend (gateway_bootstrap_canonical_information native stable discipline
    information object offset original resolved canonical).
Proof.
  intros before world after next INFO INTERFERENCE.
  destruct (@gateway_thread_ambient World Event backend io native stable discipline thread_errno
    runtime None before world after next (proj1 (proj1 (proj1 INFO))) INTERFERENCE)
    as [SIDE [ACCESS FRAME]].
  eapply gateway_bootstrap_canonical_retained; eassumption.
Qed.
