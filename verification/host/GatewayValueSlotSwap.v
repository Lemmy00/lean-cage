(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The size word protects the same actual tag slot through its read. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayValueEntry GatewayValueStack.

Definition gateway_value_swap_slots slots :gateway_value_slots:={|
  gateway_value_tag_slot:=gateway_value_size_slot slots;gateway_value_size_slot:=gateway_value_tag_slot slots|}.

Lemma gateway_value_slots_involution slots :gateway_value_swap_slots(gateway_value_swap_slots slots)=slots.
Proof. destruct slots;reflexivity. Qed.

Theorem gateway_value_active_swap {World}native stable discipline slots stream_block stream_offset
    initial readonly original memory world :
  @gateway_value_active World native stable discipline slots stream_block stream_offset initial readonly original memory world ->
  gateway_value_active native stable discipline(gateway_value_swap_slots slots)stream_block stream_offset initial readonly original memory world.
Proof.
  intros[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN[DIFFERENT[TAG_STREAM[SIZE_STREAM[TAG_READ SIZE_READ]]]]]]]]].
  split;[exact CONTEXT|]. split;[exact SIZE|]. split;[exact TAG|].
  split;[exact SIZE_OWN|]. split;[exact TAG_OWN|].
  split;[change(gateway_value_size_slot slots<>gateway_value_tag_slot slots);congruence|].
  split;[exact SIZE_STREAM|]. split;[exact TAG_STREAM|]. split;assumption.
Qed.
