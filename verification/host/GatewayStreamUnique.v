(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: One actual initialized stream memory has one field value tuple. *)
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayStreamInterface.

Theorem gateway_stream_memory_unique memory object offset first second :
  gateway_stream_memory memory object offset first ->gateway_stream_memory memory object offset second ->first=second.
Proof.
  destruct first,second;unfold gateway_stream_memory;cbn.
  intros(A &B &C &D &E &F &G &H)(I &J &K &L &M &N &O &P);f_equal;congruence.
Qed.
