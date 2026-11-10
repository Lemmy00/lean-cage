(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Transfer completion retains the actual stream and interpreter owner. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayStreamInterface GatewayStreamRelations GatewayReadContext.
Open Scope Z_scope.

Definition gateway_transfer_state {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    stream_block stream_offset data_block readonly initial memory world :Prop:=
  exists final,gateway_stream_memory memory stream_block stream_offset final /\
    gateway_stream_transport_after initial final /\discipline None memory world /\
    native_private world stream_block /\native_private world data_block /\Mem.valid_block memory data_block /\
    (forall object position,readonly object position->stable_readonly world object position).

Lemma gateway_transfer_state_from_context {World}native_private stable_readonly discipline
    stream_block stream_offset data_block offset amount readonly large initial final memory world :
  @gateway_read_context World native_private stable_readonly discipline None stream_block stream_offset final
    data_block offset amount large memory world ->
  (forall object position,readonly object position->large object position) ->
  gateway_stream_transport_after initial final ->
  gateway_transfer_state native_private stable_readonly discipline stream_block stream_offset data_block readonly
    initial memory world.
Proof.
  intros[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]]INCLUDED TRANSPORT.
  exists final;split;[exact(gateway_read_stream_cells _ _ _ _ _ _ _ _ INPUT)|].
  split;[exact TRANSPORT|]. split;[exact SIDE|]. split;[exact STREAM|]. split;[exact DATA|].
  split;[exact(gateway_read_data_live _ _ _ _ _ _ _ _ INPUT)|].
  intros object position HERE;apply IMMUTABLE;apply INCLUDED;exact HERE.
Qed.

Lemma gateway_transfer_state_transport {World}native_private stable_readonly discipline
    stream_block stream_offset data_block readonly initial middle memory world :
  gateway_stream_transport_after initial middle ->
  @gateway_transfer_state World native_private stable_readonly discipline stream_block stream_offset data_block readonly
    middle memory world ->
  gateway_transfer_state native_private stable_readonly discipline stream_block stream_offset data_block readonly
    initial memory world.
Proof.
  intros TRANSPORT[final[CELLS[RELATION REST]]].
  exists final;split;[exact CELLS|]. split;[eapply gateway_transport_transitive;[exact TRANSPORT|exact RELATION]|exact REST].
Qed.
