(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The actual retained child slot supplies the spawn output
   authority. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI GatewaySpawnActions
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnFrames GatewayPairContext GatewaySDKInputs GatewaySDKVectors
  GatewayExchangeStorage GatewayExchangeScope GatewayCallerFamily GatewaySpawnVectorMemory GatewayVectorCells.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_spawn_child_slot {World Event}(backend:gateway_backend World Event)io native stable discipline resources ipc
    builders genuine footprint(sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint)
    readonly reference owner environment data control actions attributes blocks symbols data_identity control_identity
    data_left data_right control_left control_right plan settings memory world:
  gateway_exchange_storage native stable readonly reference owner environment data control actions attributes blocks symbols->
  gateway_sdk_context native stable discipline resources ipc readonly(exchange_selected_block environment)reference owner(resources owner)
    data_identity control_identity data control data_left data_right control_left control_right builders genuine
    (Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings))memory world->
  native world(spawn_child_block blocks) /\
  gateway_native_pointer memory(spawn_child_block blocks)Ptrofs.zero 4 Writable /\
  Mem.valid_access memory Mint32(spawn_child_block blocks)0 Writable /\
  (forall position,~footprint world(spawn_child_block blocks)position).
Proof.
  intros STORAGE[FLAGS[GENUINE[ACT ATTR]]].
  set(cell:={|vector_cell_block:=spawn_child_block blocks;vector_cell_offset:=0;vector_cell_chunk:=Mint32;
    vector_cell_value:=Vint Int.zero|}).
  assert(MEMBER:In cell(gateway_spawn_cell_plan blocks symbols))by(left;reflexivity).
  pose proof(exchange_storage_cells native stable readonly reference owner environment data control actions attributes blocks symbols STORAGE cell MEMBER)as CELLS.
  destruct CELLS as[SELECTED[AWAY_DATA[AWAY_CONTROL[AWAY_ACTIONS[AWAY_ATTRIBUTES READONLY]]]]].
  destruct((proj1(proj2 FLAGS))(spawn_child_block blocks)SELECTED)as[LIVE[NATIVE[IMMUTABLE[[FRAME CURRENT]REST]]]].
  assert(ORIGINAL:gateway_vector_writable reference cell).
  { eapply Forall_forall;[exact(exchange_storage_access native stable readonly reference owner environment data control actions attributes blocks symbols STORAGE)|exact MEMBER]. }
  destruct ORIGINAL as[RANGE ALIGN].
  assert(ACCESS:Mem.valid_access memory Mint32(spawn_child_block blocks)0 Writable).
  { split;[|exact ALIGN]. intros position INSIDE.
    apply(proj1(CURRENT(spawn_child_block blocks)(or_introl eq_refl)position Cur Writable));apply RANGE;exact INSIDE. }
  split;[exact NATIVE|]. split.
  - split;[lia|]. split;[change(4<=18446744073709551616);lia|]. split;[exact LIVE|exact(proj1 ACCESS)].
  - split;[exact ACCESS|]. change(spawn_child_block blocks<>actions)in AWAY_ACTIONS.
    change(spawn_child_block blocks<>attributes)in AWAY_ATTRIBUTES.
    eapply gateway_builder_other_block;
      [exact sdk|exact GENUINE|exact NATIVE|].
    split;intros offset recorded SAME;[rewrite ACT in SAME|rewrite ATTR in SAME];inversion SAME;congruence.
Qed.
