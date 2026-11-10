(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Compose actual readonly, permission and native-owner observations. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayThreadRuntime GatewayBufferReference GatewayPrefixBuffer.
Open Scope Z_scope.

Record gateway_transport_frame {World}(native_private:World->block->Prop)readonly
    stream_block stream_offset data_block base total before world after next :Prop:={
  gateway_transport_readonly:Mem.unchanged_on readonly before after;
  gateway_transport_stream_permissions:gateway_native_permissions before after stream_block stream_offset 48;
  gateway_transport_data_permissions:gateway_native_permissions before after data_block base total;
  gateway_transport_native:gateway_native_reference native_private before world after next
}.

Lemma gateway_transport_frame_refl {World}native_private readonly stream_block stream_offset data_block base total memory world :
  @gateway_transport_frame World native_private readonly stream_block stream_offset data_block base total memory world memory world.
Proof.
  constructor;[apply Mem.unchanged_on_refl|unfold gateway_native_permissions;intros;reflexivity|
    unfold gateway_native_permissions;intros;reflexivity|apply gateway_native_reference_refl].
Qed.

Lemma gateway_transport_frame_transitive {World}native_private readonly stream_block stream_offset data_block base total
    before world middle current after next :
  @gateway_transport_frame World native_private readonly stream_block stream_offset data_block base total before world middle current ->
  gateway_transport_frame native_private readonly stream_block stream_offset data_block base total middle current after next ->
  gateway_transport_frame native_private readonly stream_block stream_offset data_block base total before world after next.
Proof.
  intros[FIRST_RO FIRST_STREAM FIRST_DATA FIRST_NATIVE][SECOND_RO SECOND_STREAM SECOND_DATA SECOND_NATIVE];constructor.
  - eapply Mem.unchanged_on_trans;[exact FIRST_RO|exact SECOND_RO].
  - eapply gateway_native_permissions_transitive;[exact FIRST_STREAM|exact SECOND_STREAM].
  - eapply gateway_native_permissions_transitive;[exact FIRST_DATA|exact SECOND_DATA].
  - eapply gateway_native_reference_transitive;[exact FIRST_NATIVE|exact SECOND_NATIVE].
Qed.

Lemma gateway_transport_frame_buffers {World}native_private readonly protected
    stream_block stream_offset data_block base total before world after next :
  (forall object position,readonly object position->protected object position) ->
  gateway_buffer_reference protected stream_block data_block before after ->
  @gateway_native_reference World native_private before world after next ->
  gateway_transport_frame native_private readonly stream_block stream_offset data_block base total before world after next.
Proof.
  intros INCLUDED BUFFER NATIVE;constructor.
  - eapply Mem.unchanged_on_implies;[exact(proj1 BUFFER)|]. intros object position HERE LIVE;apply INCLUDED;exact HERE.
  - eapply gateway_buffer_native_permissions;[exact BUFFER|left;reflexivity].
  - eapply gateway_buffer_native_permissions;[exact BUFFER|right;reflexivity].
  - exact NATIVE.
Qed.
