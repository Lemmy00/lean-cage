(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Readiness protects the caller data through a zero-length internal view. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayStreamInterface GatewayReadyInterface GatewayReadMemory GatewayThreadRuntime.
Open Scope Z_scope.

Definition gateway_ready_protected readonly data_block data_offset amount object position : Prop :=
  readonly object position \/ gateway_data_region data_block data_offset amount object position.

Lemma gateway_ready_protected_inputs before stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
  gateway_read_inputs before stream_block stream_offset initial stream_block Ptrofs.zero 0
    (gateway_ready_protected readonly data_block data_offset amount).
Proof.
  intro INPUT; pose proof (gateway_read_stream_live _ _ _ _ _ _ _ _ INPUT) as STREAM_LIVE.
  destruct INPUT as [CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
  pose proof (Ptrofs.unsigned_range stream_offset) as STREAM_OFFSET.
  constructor.
  - exact CELLS.
  - split; [lia |vm_compute; discriminate].
  - exact STREAM_BOUND.
  - vm_compute; discriminate.
  - exact STREAM_PERM.
  - exact STREAM_LIVE.
  - cbn; intros position RANGE; lia.
  - right; left; change (0 <= Ptrofs.unsigned stream_offset); lia.
  - intros object position [HERE |[SAME RANGE]]; [apply READONLY_LIVE with (position := position); exact HERE |].
    subst object; exact DATA_LIVE.
  - intros object position [HERE |[SAME RANGE]]; [apply READONLY_READABLE; exact HERE |].
    subst object; eapply Mem.perm_implies; [apply DATA_PERM; exact RANGE |constructor].
  - cbn; intros position RANGE; lia.
  - intros position RANGE [HERE |[SAME DATA_RANGE]]; [exact (READONLY_REMAINING position RANGE HERE) |].
    subst data_block; destruct SEPARATE as [DIFFERENT |[BEFORE |AFTER]]; [contradiction |lia |lia].
  - intros position RANGE [HERE |[SAME DATA_RANGE]]; [exact (READONLY_CANCEL position RANGE HERE) |].
    subst data_block; destruct SEPARATE as [DIFFERENT |[BEFORE |AFTER]]; [contradiction |lia |lia].
Qed.

Lemma gateway_ready_protected_stable {World Event} (backend : GatewayMachine.gateway_backend World Event) io
    native_private stable_readonly discipline thread_errno
    (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    before world data_block data_offset amount readonly :
  discipline None before world -> native_private world data_block ->
  (forall object position, readonly object position -> stable_readonly world object position) ->
  forall object position, gateway_ready_protected readonly data_block data_offset amount object position ->
    stable_readonly world object position.
Proof.
  intros SIDE PRIVATE IMMUTABLE object position [HERE |[SAME RANGE]]; [apply IMMUTABLE; exact HERE |].
  subst object; eapply gateway_thread_native_stable; [exact runtime |exact SIDE |exact PRIVATE].
Qed.

Theorem gateway_ready_recover_inputs before after stream_block stream_offset initial final data_block data_offset amount readonly
    (protected : block -> Z -> Prop) :
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
  gateway_read_inputs after stream_block stream_offset final stream_block Ptrofs.zero 0 protected ->
  (forall object position, gateway_ready_protected readonly data_block data_offset amount object position -> protected object position) ->
  Mem.unchanged_on protected before after -> Mem.valid_block after data_block ->
  gateway_read_inputs after stream_block stream_offset final data_block data_offset amount readonly.
Proof.
  intros INPUT OUTPUT INCLUDED FRAME LIVE.
  destruct INPUT as [CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
  constructor.
  - exact (gateway_read_stream_cells _ _ _ _ _ _ _ _ OUTPUT).
  - exact SIZE.
  - exact STREAM_BOUND.
  - exact DATA_BOUND.
  - exact (gateway_read_stream_owned _ _ _ _ _ _ _ _ OUTPUT).
  - exact LIVE.
  - intros position RANGE; eapply Mem.perm_unchanged_on; [exact FRAME | |apply DATA_PERM; exact RANGE].
    apply INCLUDED; right; split; [reflexivity |exact RANGE].
  - exact SEPARATE.
  - intros object position HERE; apply (gateway_read_readonly_live _ _ _ _ _ _ _ _ OUTPUT object position).
    apply INCLUDED; left; exact HERE.
  - intros object position HERE; apply (gateway_read_readonly_readable _ _ _ _ _ _ _ _ OUTPUT object position).
    apply INCLUDED; left; exact HERE.
  - exact READONLY_DATA.
  - exact READONLY_REMAINING.
  - exact READONLY_CANCEL.
Qed.
