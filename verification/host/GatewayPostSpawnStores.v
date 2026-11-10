(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual stream stores preserve all remaining caller allocations and leases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayCallerBuffers GatewayCallerFamily
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayPostSpawnContext GatewayPostSpawnCleanup GatewayPairContext.
Open Scope Z_scope.

Theorem gateway_postspawn_store {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources
    builders genuine footprint(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint)
    readonly selected reference owner data control data_left data_right control_left control_right leases
    before world after object position chunk value:
  gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
    data control data_left data_right control_left control_right postspawn_empty_builders leases before world->
  selected object->object<>data->object<>control->(forall position,~readonly object position)->
  Mem.store chunk before object position value=Some after->
  gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
    data control data_left data_right control_left control_right postspawn_empty_builders leases after world.
Proof.
  intros[SIDE VALID GENUINE SHADOW FAMILY DATA CONTROL LEASES]SELECTED AWAY_DATA AWAY_CONTROL DISJOINT STORE.
  constructor;try assumption.
  - eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact(proj1(proj2(FAMILY object SELECTED)))|exact STORE].
  - apply(gateway_builder_empty _ _ _ _ _ _ _ _ _ sdk after world);rewrite SHADOW;reflexivity.
  - intros target MEMBER;eapply gateway_caller_buffers_store;[exact(FAMILY target MEMBER)|exact STORE|exact DISJOINT].
  - eapply gateway_pair_cells_unchanged;[exact DATA|].
    eapply Mem.store_unchanged_on;[exact STORE|]. intros offset RANGE[SAME OTHER];congruence.
  - eapply gateway_pair_cells_unchanged;[exact CONTROL|].
    eapply Mem.store_unchanged_on;[exact STORE|]. intros offset RANGE[SAME OTHER];congruence.
Qed.
