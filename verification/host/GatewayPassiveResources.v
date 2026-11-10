(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual native observers preserve protected descriptor leases. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewaySpawnResources GatewaySpawnRuntime
  GatewayPairHistory.
Import ListNotations.

(* These operations can change user buffers, clocks, errno and socket queues.
   This classification concerns only descriptor/OFD identity and status flags;
   it asserts no memory, I/O-byte, progress or whole-helper property. *)
Definition gateway_resource_observer (definition : Ctypes.fundef Clight.function) : Prop :=
  In definition [gateway_clock_gettime_definition; gateway_errno_location_definition;
    gateway_poll_definition; gateway_send_definition; gateway_receive_definition].

Record gateway_passive_resource_runtime {World Event} (backend : gateway_backend World Event)
    (resources : World -> gateway_resource_state) : Prop := {
  gateway_resource_observer_operation : forall definition arguments before world result after next observed,
    gateway_resource_valid (resources world) -> gateway_resource_observer definition ->
    gateway_runtime_operation backend definition arguments before world result after next observed ->
    gateway_resource_valid (resources next) /\
    gateway_resource_frame (resources world) (resources next) (fun _ => False) (fun _ => False) /\
    gateway_resource_status_frame (resources world) (resources next) (fun _ => False) /\
    gateway_exclusive_kept (resources world) (resources next)
}.

Theorem gateway_passive_resource_reference {World Event} (backend : gateway_backend World Event) resources
    (runtime : gateway_passive_resource_runtime backend resources)
    definition arguments before world result after next observed :
  gateway_resource_valid (resources world) -> gateway_resource_observer definition ->
  gateway_runtime_operation backend definition arguments before world result after next observed ->
  gateway_resource_valid (resources next) /\ gateway_resource_reference (resources world) (resources next).
Proof.
  intros VALID OBSERVER OPERATION.
  destruct (gateway_resource_observer_operation _ _ runtime _ _ _ _ _ _ _ _ VALID OBSERVER OPERATION)
    as [NEXT [FRAME [STATUS EXCLUSIVE]]].
  split; [exact NEXT |].
  eapply gateway_resource_reference_step; [apply gateway_resource_reference_refl |exact FRAME | |exact STATUS |exact EXCLUSIVE].
  intros; tauto.
Qed.

Corollary gateway_clock_resources {World Event} (backend : gateway_backend World Event) resources
    (runtime : gateway_passive_resource_runtime backend resources)
    arguments before world result after next observed :
  gateway_resource_valid (resources world) ->
  gateway_runtime_operation backend gateway_clock_gettime_definition arguments before world result after next observed ->
  gateway_resource_valid (resources next) /\ gateway_resource_reference (resources world) (resources next).
Proof.
  intros VALID OPERATION; eapply gateway_passive_resource_reference; [exact runtime |exact VALID | |exact OPERATION].
  unfold gateway_resource_observer; left; reflexivity.
Qed.
