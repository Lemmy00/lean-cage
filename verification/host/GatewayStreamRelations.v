(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Repeated cancellation checks preserve the same data budget. *)
From Stdlib Require Import ZArith.
From HostGateway Require Import GatewayStreamInterface.

Lemma gateway_transport_refl initial:gateway_stream_transport_after initial initial.
Proof. unfold gateway_stream_transport_after;repeat split;auto. Qed.

Lemma gateway_transport_transitive initial middle final :
  gateway_stream_transport_after initial middle ->gateway_stream_transport_after middle final ->
  gateway_stream_transport_after initial final.
Proof. unfold gateway_stream_transport_after;intuition congruence. Qed.

Lemma gateway_transport_descriptor initial final :
  gateway_stream_transport_after initial final ->stream_descriptor final=stream_descriptor initial.
Proof. intro TRANSPORT;exact(proj1 TRANSPORT). Qed.

Lemma gateway_read_after_transport initial middle amount final :
  gateway_stream_transport_after initial middle ->gateway_stream_read_after middle amount final ->
  gateway_stream_read_after initial amount final.
Proof. unfold gateway_stream_transport_after,gateway_stream_read_after;intuition congruence. Qed.
