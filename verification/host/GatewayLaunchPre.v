(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Strong caller inputs refine the same checked launch path. *)
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayFramedRuntime GatewayLaunchPaths.

Theorem gateway_launch_pre {World Event}(backend:gateway_backend World Event)target property initial source:
  gateway_launch_path backend target property source->gateway_ambient_closed backend initial->
  (forall memory world,initial memory world->property memory world)->
  gateway_launch_path backend target initial source.
Proof.
  intros SCRIPT CLOSED INCLUDED;inversion SCRIPT;subst.
  - eapply gateway_launch_reached;intros memory world READY;apply H,INCLUDED;exact READY.
  - eapply gateway_launch_failure;eassumption.
  - eapply gateway_launch_symbolic_failure;eassumption.
  - eapply gateway_launch_stuck;[exact CLOSED|exact H0|exact H1|].
    intros memory world trace after READY;apply H2 with(world:=world);apply INCLUDED;exact READY.
  - eapply gateway_launch_next with(following:=following)(middle:=middle);[exact CLOSED|exact H0|exact H1| |exact H3].
    intros memory world READY;apply H2,INCLUDED;exact READY.
  - eapply gateway_launch_external;[exact H|exact CLOSED|].
    intros before world returned after next observed READY OPERATION.
    eapply H1;[apply INCLUDED;exact READY|exact OPERATION].
  - eapply gateway_launch_helper_call;[exact H|].
    intros before world events returned after next READY RUN.
    eapply H0;[apply INCLUDED;exact READY|exact RUN].
Qed.
