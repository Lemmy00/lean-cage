(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Cancellation uses a distinct actual control descriptor. *)
From compcert Require Import Integers.
From HostGateway Require Import GatewayStreamInterface.

Class gateway_distinct_channels (stream : gateway_stream_values) : Prop :=
  gateway_channels_distinct : stream_descriptor stream <> stream_control stream.

Lemma gateway_distinct_channels_retained initial current :
  gateway_distinct_channels initial -> gateway_stream_transport_after initial current ->
  gateway_distinct_channels current.
Proof.
  intros DISTINCT [DATA [CONTROL REST]].
  change (stream_descriptor current <> stream_control current).
  rewrite DATA, CONTROL; exact DISTINCT.
Qed.
