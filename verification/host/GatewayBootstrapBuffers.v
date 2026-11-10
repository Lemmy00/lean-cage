(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Every bootstrap buffer and literal survives the actual disjoint writes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapRuntime GatewayBootstrapCapacities
  GatewayBootstrapEffects GatewayBootstrapRetention GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_buffers {World} native stable (discipline : option val -> mem -> World -> Prop)
    (buffers : list (block * Z * permission)) (literals : list (block * list Byte.int)) memory (world : World) : Prop :=
  discipline None memory world /\
  (forall object amount access, In (object, amount, access) buffers ->
    gateway_bootstrap_capacity native memory world object Ptrofs.zero amount access) /\
  (forall object bytes, In (object, bytes) literals ->
    gateway_bootstrap_protected native stable memory world (Vptr object Ptrofs.zero) bytes).

Theorem gateway_bootstrap_capacity_span {World} native memory world object amount low count :
  @gateway_bootstrap_capacity World native memory world object Ptrofs.zero amount Writable ->
  0 <= low -> 0 <= count -> low + count <= amount -> low < Ptrofs.modulus ->
  gateway_native_pointer memory object (Ptrofs.repr low) count Writable.
Proof.
  intros [PRIVATE [POSITIVE [NONNEGATIVE [BOUND [LIVE RANGE]]]]] LOW COUNT END WIDTH.
  unfold gateway_native_pointer.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  split; [exact COUNT |]. split; [change (0 + amount <= Ptrofs.modulus) in BOUND; lia |].
  split; [exact LIVE |]. intros position INSIDE; apply RANGE; change (0 <= position < 0 + amount); lia.
Qed.

Theorem gateway_bootstrap_buffers_effect {World} native stable discipline buffers literals
    before world after next destination offset count :
  @gateway_bootstrap_buffers World native stable discipline buffers literals before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable (gateway_native_region destination offset count) world before after ->
  gateway_native_permissions before after destination offset count ->
  (forall object bytes, In (object, bytes) literals -> object <> destination) ->
  gateway_bootstrap_buffers native stable discipline buffers literals after next.
Proof.
  intros [SIDE [CAPACITIES LITERALS]] NEXT ACCESS FRAME PERMISSIONS SEPARATE.
  split; [exact NEXT |]. split.
  - intros object amount access MEMBER; eapply gateway_bootstrap_capacity_copy;
      [apply CAPACITIES with (access := access); exact MEMBER |exact ACCESS |exact FRAME |exact PERMISSIONS].
  - intros object bytes MEMBER; eapply gateway_bootstrap_protected_effect;
      [apply LITERALS; exact MEMBER |exact ACCESS |exact FRAME |].
    intros position RANGE [SAME WRITE]; eapply (SEPARATE object bytes MEMBER); exact SAME.
Qed.

Theorem gateway_bootstrap_buffers_quiet {World} native stable discipline buffers literals
    before world after next :
  @gateway_bootstrap_buffers World native stable discipline buffers literals before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_buffers native stable discipline buffers literals after next.
Proof.
  intros [SIDE [CAPACITIES LITERALS]] NEXT ACCESS FRAME.
  split; [exact NEXT |]. split.
  - intros object amount access MEMBER; eapply gateway_bootstrap_capacity_quiet;
      [apply CAPACITIES with (access := access); exact MEMBER |exact ACCESS |exact FRAME].
  - intros object bytes MEMBER; eapply gateway_bootstrap_protected_retained;
      [apply LITERALS; exact MEMBER |exact ACCESS |exact FRAME].
Qed.

Theorem gateway_bootstrap_buffers_ambient {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno) buffers literals :
  gateway_ambient_closed backend (gateway_bootstrap_buffers native stable discipline buffers literals).
Proof.
  intros before world after next INPUT INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next (proj1 INPUT) INTERFERENCE)
    as [SIDE [ACCESS FRAME]].
  eapply gateway_bootstrap_buffers_quiet; eassumption.
Qed.

Theorem gateway_bootstrap_capacity_weaken {World} native memory world object offset amount first last :
  @gateway_bootstrap_capacity World native memory world object offset amount first ->
  perm_order first last -> gateway_bootstrap_capacity native memory world object offset amount last.
Proof.
  intros [PRIVATE [POSITIVE [NONNEGATIVE [BOUND [LIVE RANGE]]]]] ORDER.
  split; [exact PRIVATE |]. split; [exact POSITIVE |]. split; [exact NONNEGATIVE |].
  split; [exact BOUND |]. split; [exact LIVE |].
  intros position INSIDE; eapply Mem.perm_implies; [apply RANGE; exact INSIDE |exact ORDER].
Qed.
