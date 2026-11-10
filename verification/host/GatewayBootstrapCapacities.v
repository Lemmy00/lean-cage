(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Copies retain full native capacities outside and inside their actual writes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayBootstrapRuntime GatewayThreadRuntime.
Open Scope Z_scope.

Definition gateway_bootstrap_capacity {World} (native : World -> block -> Prop)
    memory world object offset amount permission : Prop :=
  native world object /\ 0 < amount /\ gateway_native_pointer memory object offset amount permission.

Theorem gateway_bootstrap_capacity_copy {World} native stable before world after next
    destination destination_offset count object offset amount permission :
  @gateway_bootstrap_capacity World native before world object offset amount permission ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable
    (gateway_native_region destination destination_offset count) world before after ->
  gateway_native_permissions before after destination destination_offset count ->
  gateway_bootstrap_capacity native after next object offset amount permission.
Proof.
  intros [PRIVATE [POSITIVE [NONNEGATIVE [BOUND [LIVE RANGE]]]]] ACCESS FRAME PERMISSIONS.
  assert (KEEP : forall position,
    Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + amount ->
    Mem.perm after object position Cur permission).
  { intros position INSIDE.
    destruct (Pos.eq_dec object destination) as [SAME |DIFFERENT].
    - subst object.
      destruct (zle (Ptrofs.unsigned destination_offset) position) as [LOW |LOW];
        destruct (zlt position (Ptrofs.unsigned destination_offset + count)) as [HIGH |HIGH].
      + apply (proj1 (PERMISSIONS position Cur permission ltac:(lia))); apply RANGE; exact INSIDE.
      + eapply Mem.perm_unchanged_on;
          [exact FRAME |split; [left; exact PRIVATE |intros [_ WRITE]; lia] |apply RANGE; exact INSIDE].
      + eapply Mem.perm_unchanged_on;
          [exact FRAME |split; [left; exact PRIVATE |intros [_ WRITE]; lia] |apply RANGE; exact INSIDE].
      + eapply Mem.perm_unchanged_on;
          [exact FRAME |split; [left; exact PRIVATE |intros [_ WRITE]; lia] |apply RANGE; exact INSIDE].
    - eapply Mem.perm_unchanged_on;
        [exact FRAME |split; [left; exact PRIVATE |intros [SAME _]; contradiction] |apply RANGE; exact INSIDE]. }
  split; [exact (proj1 ACCESS object LIVE PRIVATE) |]. split; [exact POSITIVE |].
  split; [exact NONNEGATIVE |]. split; [exact BOUND |]. split; [|exact KEEP].
  eapply Mem.perm_valid_block; apply (KEEP (Ptrofs.unsigned offset)); lia.
Qed.

Theorem gateway_bootstrap_capacity_quiet {World} native stable before world after next
    object offset amount permission :
  @gateway_bootstrap_capacity World native before world object offset amount permission ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_capacity native after next object offset amount permission.
Proof.
  intros [PRIVATE [POSITIVE [NONNEGATIVE [BOUND [LIVE RANGE]]]]] ACCESS FRAME.
  assert (KEEP : forall position,
    Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + amount ->
    Mem.perm after object position Cur permission).
  { intros position INSIDE; eapply Mem.perm_unchanged_on;
      [exact FRAME |split; [left; exact PRIVATE |cbn; tauto] |apply RANGE; exact INSIDE]. }
  split; [exact (proj1 ACCESS object LIVE PRIVATE) |]. split; [exact POSITIVE |].
  split; [exact NONNEGATIVE |]. split; [exact BOUND |]. split; [|exact KEEP].
  eapply Mem.perm_valid_block; apply (KEEP (Ptrofs.unsigned offset)); lia.
Qed.

Theorem gateway_bootstrap_capacity_store {World} (native : World -> block -> Prop)
    before after world object offset amount permission chunk destination position value :
  gateway_bootstrap_capacity native before world object offset amount permission ->
  Mem.store chunk before destination position value = Some after ->
  gateway_bootstrap_capacity native after world object offset amount permission.
Proof.
  intros [PRIVATE [POSITIVE [NONNEGATIVE [BOUND [LIVE RANGE]]]]] STORE.
  split; [exact PRIVATE |]. split; [exact POSITIVE |]. split; [exact NONNEGATIVE |].
  split; [exact BOUND |]. split.
  - eapply Mem.store_valid_block_1; eassumption.
  - intros selected INSIDE; eapply Mem.perm_store_1; [exact STORE |apply RANGE; exact INSIDE].
Qed.
