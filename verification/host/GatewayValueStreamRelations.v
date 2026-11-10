(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Scalar stream receipts retain each actual counter update in order. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers.
From HostGateway Require Import GatewayStreamInterface GatewayValueNodeMemory.
Open Scope Z_scope.

Definition gateway_scalar_stream_after initial width amount final :Prop:=
  exists tagged sized,gateway_stream_read_after(gateway_stream_node_debit initial)1 tagged /\
    gateway_stream_read_after tagged width sized /\gateway_stream_read_after sized amount final.

Lemma gateway_scalar_stream_nodes initial width amount final :
  gateway_scalar_stream_after initial width amount final ->
  stream_nodes final=Int64.sub(stream_nodes initial)Int64.one.
Proof.
  intros[tagged[sized[[A[B[C[D[NODES_TAG REST_TAG]]]]][[E[F[G[H[NODES_SIZE REST_SIZE]]]]]
    [I[J[K[L[NODES_FINAL REST_FINAL]]]]]]]]].
  rewrite NODES_FINAL,NODES_SIZE,NODES_TAG;reflexivity.
Qed.

Lemma gateway_scalar_stream_descriptor initial width amount final :
  gateway_scalar_stream_after initial width amount final ->stream_descriptor final=stream_descriptor initial.
Proof. intros[tagged[sized[[TAG REST_TAG][[SIZE REST_SIZE][FINAL REST_FINAL]]]]]. rewrite FINAL,SIZE,TAG;reflexivity. Qed.
