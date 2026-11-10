(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The byte-reader inputs come from the value call's actual fresh slots. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayValueEntry GatewayValueContext GatewayStreamInterface GatewayWordInputs
  GatewayWordContext.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_value_tag_word_inputs memory slots stream_block stream_offset initial readonly :
  gateway_value_inputs memory stream_block stream_offset initial readonly ->
  Mem.range_perm memory(gateway_value_tag_slot slots)0 8 Cur Freeable ->
  gateway_value_tag_slot slots<>stream_block ->(forall position,~readonly(gateway_value_tag_slot slots)position) ->
  gateway_word_inputs memory stream_block stream_offset initial(gateway_value_tag_slot slots)Ptrofs.zero readonly.
Proof.
  intros INPUT TAG_OWN DIFFERENT OUTSIDE;split;[|change(8|0);exists 0;reflexivity].
  constructor.
  - exact(gateway_value_stream_cells _ _ _ _ _ INPUT).
  - change(0<=8<=Int64.max_unsigned);unfold Int64.max_unsigned,Int64.modulus,Int64.wordsize;cbn;lia.
  - exact(gateway_value_stream_bounds _ _ _ _ _ INPUT).
  - change(8<=18446744073709551616);lia.
  - exact(gateway_value_stream_owned _ _ _ _ _ INPUT).
  - eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia.
  - intros position RANGE;eapply Mem.perm_implies;[apply TAG_OWN;exact RANGE|constructor].
  - left;congruence.
  - exact(gateway_value_readonly_live _ _ _ _ _ INPUT).
  - exact(gateway_value_readonly_readable _ _ _ _ _ INPUT).
  - intros position RANGE;apply OUTSIDE.
  - intros position RANGE;eapply gateway_value_readonly_counters;[exact INPUT|lia].
  - exact(gateway_value_readonly_cancel _ _ _ _ _ INPUT).
Qed.

Theorem gateway_value_allocated_word_context {World}
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    slots stream_block stream_offset initial readonly original memory world :
  gateway_value_allocated native stable discipline slots stream_block stream_offset initial readonly original memory world ->
  gateway_word_context native stable discipline stream_block stream_offset initial
    (gateway_value_tag_slot slots)Ptrofs.zero readonly original memory world.
Proof.
  intros[[SIDE[STREAM[READONLY[INPUT FRAME]]]][TAG[SIZE[TAG_OWN[SIZE_OWN[DIFFERENT[TAG_STREAM[SIZE_STREAM[TAG_READ SIZE_READ]]]]]]]]].
  split;[exact SIDE|]. split;[exact STREAM|]. split;[exact TAG|]. split;[exact READONLY|].
  split;[eapply gateway_value_tag_word_inputs;eassumption|exact FRAME].
Qed.
