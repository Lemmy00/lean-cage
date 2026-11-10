(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Retain actual read inputs from their precise protected region. *)
From Stdlib Require Import ZArith.
From compcert Require Import AST Values Memory.
From HostGateway Require Import GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayThreadRuntime.

Theorem gateway_read_context_region_preserved {World} (native_private : World -> block -> Prop)
    stable_readonly discipline mode stream_block stream_offset initial data_block data_offset amount readonly
    before world after next :
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly before world ->
  discipline mode after next -> gateway_access_retained native_private stable_readonly before world next ->
  Mem.unchanged_on (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly after next.
Proof.
  intros [SIDE [STREAM [DATA [IMMUTABLE INPUT]]]] AFTER [NATIVE STABLE] FRAME.
  split; [exact AFTER |]. split.
  - apply NATIVE; [eapply gateway_read_stream_live; exact INPUT | exact STREAM].
  - split.
    + apply NATIVE; [exact (gateway_read_data_live _ _ _ _ _ _ _ _ INPUT) | exact DATA].
    + split.
      * intros object position HERE; apply STABLE.
        -- exact (gateway_read_readonly_readable _ _ _ _ _ _ _ _ INPUT object position HERE).
        -- apply IMMUTABLE; exact HERE.
      * eapply gateway_read_inputs_unchanged; eassumption.
Qed.

Theorem gateway_read_context_output_frame {World} (native_private : World -> block -> Prop)
    stable_readonly discipline mode stream_block stream_offset initial data_block data_offset amount readonly
    output before world after next :
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly before world ->
  discipline mode after next -> gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly output world before after ->
  (forall object position,
    gateway_read_region stream_block stream_offset data_block data_offset amount readonly object position ->
    ~ output object position) ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly after next /\
  Mem.unchanged_on (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after.
Proof.
  intros INPUT SIDE ACCESS FRAME SEPARATE.
  assert (PROTECTED : Mem.unchanged_on
    (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after).
  { eapply gateway_native_frame_restrict; [exact FRAME | |exact SEPARATE].
    intros object position [STREAM | [DATA | READONLY]].
    - destruct STREAM as [SAME RANGE]; subst object; left; exact (proj1 (proj2 INPUT)).
    - destruct DATA as [SAME RANGE]; subst object; left; exact (proj1 (proj2 (proj2 INPUT))).
    - right; apply (proj1 (proj2 (proj2 (proj2 INPUT)))); exact READONLY. }
  split; [eapply gateway_read_context_region_preserved; eassumption | exact PROTECTED].
Qed.
