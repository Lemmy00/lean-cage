(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A terminal source return retains an ambient-closed caller property. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_terminal_return_scope {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) returned :
  gateway_ambient_closed backend property ->
  forall before world events value after next, property before world ->
  gateway_steps backend ge (gateway_live (Returnstate returned Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = returned /\ property after next.
Proof.
  intros CLOSED before world events; revert before world.
  induction events as [|event rest IH]; intros before world value after next INPUT RUN.
  - inversion RUN; subst; split; [reflexivity |exact INPUT].
  - inversion RUN; subst.
    match goal with STEP : gateway_step _ _ _ _ _ |- _ => inversion STEP; subst end; cbn in *; try contradiction.
    + match goal with REAL : step2 _ (Returnstate _ Kstop _) _ _ |- _ => inversion REAL end.
    + eapply IH; [eapply CLOSED; eassumption |eassumption].
    + match goal with TAIL : gateway_steps _ _ (gateway_dead _ _) _ _ |- _ =>
        destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ BAD] end; discriminate.
Qed.
