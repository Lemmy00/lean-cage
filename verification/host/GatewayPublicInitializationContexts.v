(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: The actual current initializer context supplies the public callback flag-cell input. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory Floats.
From HostGateway Require Import GatewayMachine GatewayInitializationRegions GatewayInitializationContext GatewayInitializationCells
  GatewayInitializationFailure.

Theorem gateway_initialization_context_public_cells {World} native stable base rooted
    symbols snapshot active complete python objects decimal_float ledger retired held current identifier pointer number memory (world : World) :
  (forall memory world, base None memory world -> rooted memory world) ->
  gateway_initialization_context native stable base symbols snapshot active complete
    python objects decimal_float ledger retired held current identifier pointer number memory world ->
  gateway_initialization_failure_context rooted native symbols active complete memory world.
Proof.
  intros ATTACHED [REGIONS REST]; split.
  - apply ATTACHED; exact (proj1 (initialization_region_buffers _ _ _ _ _ _ _ _ _ REGIONS)).
  - eapply gateway_initialization_region_cells; exact REGIONS.
Qed.
