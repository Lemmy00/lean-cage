(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The same actual spawn hands its parent four live IPC leases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI
  GatewaySpawnActions GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnProcess GatewaySpawnCall GatewaySpawnRecorded
  GatewaySpawnVectors GatewaySpawnVectorMemory GatewayVectorCells GatewayPairContext GatewayConnectionResources GatewaySDKInputs
  GatewaySDKContext GatewayExchangeStorage GatewayExchangeScope GatewayCallerFamily GatewayErrorRuntime
  GatewayPostSpawnContext GatewayPostSpawnCleanup.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_parent_ipc_leases ipc(data_identity control_identity:gateway_pair_identity ipc)
    data_left data_right control_left control_right:list(Z*gateway_resource_descriptor):=
  [(data_left,pair_left_entry ipc data_identity);(data_right,pair_right_entry ipc data_identity);
   (control_left,pair_left_entry ipc control_identity);(control_right,pair_right_entry ipc control_identity)].

Theorem gateway_actual_spawn_parent_context {World Event}(backend:gateway_backend World Event)io native stable discipline resources ipc
    builders genuine footprint births executed
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint)
    (process:gateway_spawn_process_runtime backend io native stable discipline resources builders genuine footprint births executed)
    readonly reference owner environment data control actions attributes blocks symbols data_identity control_identity
    data_left data_right control_left control_right plan settings before world result after next observed engine_bytes:
  gateway_exchange_storage native stable readonly reference owner environment data control actions attributes blocks symbols->
  gateway_sdk_context native stable discipline resources ipc readonly(exchange_selected_block environment)reference owner(resources owner)
    data_identity control_identity data control data_left data_right control_left control_right builders genuine
    (Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings))before world->
  Forall(gateway_vector_loaded before)(gateway_spawn_cell_plan blocks symbols)->
  gateway_error_cstring before(Vptr(spawn_engine_symbol symbols)Ptrofs.zero)engine_bytes->
  gateway_error_cstring before(Vptr(spawn_path_symbol symbols)Ptrofs.zero)spawn_path_bytes->
  gateway_error_cstring before(Vptr(spawn_locale_symbol symbols)Ptrofs.zero)spawn_locale_bytes->
  gateway_spawn_operation backend gateway_posix_spawn_api(gateway_spawn_call_values blocks symbols actions attributes)
    before world result after next observed->
  gateway_postspawn_context native stable discipline resources builders genuine readonly(exchange_selected_block environment)reference owner
    data control data_left data_right control_left control_right(postspawn_initial_builders actions attributes plan settings)
    (gateway_parent_ipc_leases ipc data_identity control_identity data_left data_right control_left control_right)after next /\
  io observed=None /\gateway_child_history_retained(births world)(births next) /\
  exists status(created:option(gateway_spawn_birth_receipt resources births world next engine_bytes[engine_bytes]
    [spawn_path_bytes;spawn_locale_bytes]plan settings)),result=Vint status /\
    (status=Int.zero->exists receipt,created=Some receipt /\
      Mem.load Mint32 after(spawn_child_block blocks)0=
        Some(Vint(Int.repr(gateway_child_pid(gateway_spawned_birth _ _ _ _ _ _ _ _ _ receipt))))).
Proof.
  intros STORAGE INITIAL LOADED ENGINE PATH LOCALE OPERATION.
  destruct(gateway_actual_selected_spawn backend io native stable discipline resources ipc builders genuine footprint births executed
    sdk process readonly reference owner environment data control actions attributes blocks symbols data_identity control_identity
    data_left data_right control_left control_right plan settings before world result after next observed engine_bytes
    STORAGE INITIAL LOADED ENGINE PATH LOCALE OPERATION)
    as(NORMAL&GENUINE&VALID&BUILDERS&IO&FAMILY&DATA_CELLS&CONTROL_CELLS&OWNED&HISTORY&status&created&RESULT&CHILD).
  destruct INITIAL as[FLAGS[OLD_GENUINE[ACT ATTR]]].
  destruct FLAGS as(SIDE&OLD_FAMILY&OLD_VALID&DATA_LEASES&CONTROL_LEASES&MODES&OLD_DATA&OLD_CONTROL&ORIGINAL).
  split.
  - constructor;try assumption.
    + rewrite BUILDERS;unfold postspawn_initial_builders.
      destruct(builders world)as[old_actions old_attributes];cbn in ACT,ATTR;f_equal;assumption.
    + unfold gateway_parent_ipc_leases.
      constructor;[apply OWNED;exact(gateway_pair_lease_left _ _ _ _ _ DATA_LEASES)|].
      constructor;[apply OWNED;exact(gateway_pair_lease_right _ _ _ _ _ DATA_LEASES)|].
      constructor;[apply OWNED;exact(gateway_pair_lease_left _ _ _ _ _ CONTROL_LEASES)|].
      constructor;[apply OWNED;exact(gateway_pair_lease_right _ _ _ _ _ CONTROL_LEASES)|constructor].
  - split;[exact IO|]. split;[exact HISTORY|]. exists status,created;split;assumption.
Qed.
