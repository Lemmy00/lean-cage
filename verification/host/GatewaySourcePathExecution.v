(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Checked source paths construct useful executions to their real call. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewaySourcePaths GatewayFrames.
Import ListNotations.

Theorem gateway_source_path_execution {World Event} (backend : gateway_backend World Event)
    ge definition arguments continuation property source result :
  gateway_source_path backend ge definition arguments continuation property source result ->
  forall before world, property before world -> exists events after,
    gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) events
      (gateway_live (Callstate definition arguments continuation after) world) /\ result after world.
Proof.
  intro SCRIPT; induction SCRIPT; intros before world READY.
  - exists [], before; split; [constructor |apply H; exact READY].
  - destruct (H1 before world READY) as [changed [[INTERNAL [STEP UNIQUE]] POST]].
    destruct (IHSCRIPT changed world POST) as [events [after [RUN RESULT]]].
    exists (gateway_source E0 :: events), after; split; [|exact RESULT].
    econstructor; [eapply gateway_internal; [exact INTERNAL |exact STEP] |exact RUN].
Qed.
