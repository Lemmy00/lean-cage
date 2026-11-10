(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Source memory prefixes compose with the same selected launch. *)
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayLaunchPaths.

Theorem gateway_launch_after_memory_prefix {World Event}(backend:gateway_backend World Event)
    point post initial source target:
  gateway_memory_prefix backend(Clight.globalenv prog)point post initial source->
  gateway_launch_path backend target post point->gateway_launch_path backend target initial source.
Proof.
  intro PREFIX;induction PREFIX;intro REST.
  - apply gateway_launch_path_replace;exact REST.
  - eapply gateway_launch_next with(following:=following)(middle:=middle);
      [exact H|exact H0|exact I|exact H1|apply IHPREFIX;exact REST].
Qed.
