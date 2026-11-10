(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: A real native local can be protected across a nested helper. *)
From Stdlib Require Import ZArith.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayReadContext
  GatewayPrefixBuffer.
Open Scope Z_scope.

Definition gateway_local_readonly (readonly : block -> Z -> Prop) local width object position : Prop :=
  readonly object position \/ object = local /\ 0 <= position < width.

Theorem gateway_read_inputs_local memory stream_block stream_offset initial data_block data_offset amount readonly
    local width :
  gateway_read_inputs memory stream_block stream_offset initial data_block data_offset amount readonly ->
  Mem.valid_block memory local -> Mem.range_perm memory local 0 width Cur Readable ->
  local <> stream_block -> local <> data_block ->
  gateway_read_inputs memory stream_block stream_offset initial data_block data_offset amount
    (gateway_local_readonly readonly local width).
Proof.
  intros [CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL]
    LOCAL_LIVE LOCAL_PERM NOT_STREAM NOT_DATA.
  constructor; try assumption.
  - intros object position [HERE | [SAME RANGE]].
    + apply READONLY_LIVE with (position := position); exact HERE.
    + subst object; exact LOCAL_LIVE.
  - intros object position [HERE | [SAME RANGE]].
    + apply READONLY_READABLE; exact HERE.
    + subst object; apply LOCAL_PERM; exact RANGE.
  - intros position RANGE [HERE | [SAME LOCAL]];
      [exact (READONLY_DATA position RANGE HERE) | congruence].
  - intros position RANGE [HERE | [SAME LOCAL]];
      [exact (READONLY_REMAINING position RANGE HERE) | congruence].
  - intros position RANGE [HERE | [SAME LOCAL]];
      [exact (READONLY_CANCEL position RANGE HERE) | congruence].
Qed.

Theorem gateway_read_context_local {World Event} (backend : gateway_backend World Event) io
    native_private stable_readonly discipline thread_errno
    (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    mode memory world stream_block stream_offset initial data_block data_offset amount readonly local width :
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly memory world ->
  native_private world local -> Mem.valid_block memory local ->
  Mem.range_perm memory local 0 width Cur Readable -> local <> stream_block -> local <> data_block ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount (gateway_local_readonly readonly local width) memory world.
Proof.
  intros [SIDE [STREAM [DATA [IMMUTABLE INPUT]]]] PRIVATE LIVE PERMISSIONS NOT_STREAM NOT_DATA.
  split; [exact SIDE |]. split; [exact STREAM |]. split; [exact DATA |]. split.
  - intros object position [HERE | [SAME RANGE]].
    + apply IMMUTABLE; exact HERE.
    + subst object; eapply gateway_thread_native_stable; [exact runtime | exact SIDE | exact PRIVATE].
  - eapply gateway_read_inputs_local; eassumption.
Qed.

Lemma gateway_local_readonly_restrict {World} native_private stable_readonly discipline mode memory world
    stream_block stream_offset initial data_block data_offset amount readonly local width :
  @gateway_read_context World native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount (gateway_local_readonly readonly local width) memory world ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly memory world.
Proof. intro INPUT; eapply gateway_read_restrict_context; [exact INPUT | intros; left; assumption]. Qed.

Lemma gateway_local_permissions_retained readonly local width before after :
  Mem.unchanged_on (gateway_local_readonly readonly local width) before after ->
  Mem.valid_block before local ->
  forall position kind permission, 0 <= position < width ->
    Mem.perm before local position kind permission <-> Mem.perm after local position kind permission.
Proof.
  intros FRAME LIVE position kind permission RANGE.
  apply (Mem.unchanged_on_perm _ _ _ FRAME local position kind permission).
  - right; split; [reflexivity | exact RANGE].
  - exact LIVE.
Qed.
