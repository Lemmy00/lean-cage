(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real later helper progress produces the same spawn's child receipt. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI GatewaySpawnActions
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnProcess GatewaySpawnCall GatewaySpawnRecorded GatewaySpawnStatus
  GatewaySpawnVectors GatewaySpawnVectorMemory GatewayVectorCells GatewayPairContext GatewaySDKInputs GatewayExchangeStorage
  GatewayExchangeScope GatewayCallerFamily GatewayErrorRuntime.
Import ListNotations.

Theorem gateway_actual_spawn_for_helper {World Event}(backend:gateway_backend World Event)io native stable discipline resources ipc
    builders genuine footprint births executed
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint)
    (process:gateway_spawn_process_runtime backend io native stable discipline resources builders genuine footprint births executed)
    readonly reference owner environment data control actions attributes blocks symbols data_identity control_identity
    data_left data_right control_left control_right plan settings before world result after next observed engine_bytes
    allocation_before allocated temporaries later_events helper arguments continuation final final_world:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
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
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate result(gateway_spawn_call_cont environment temporaries Kstop)after)next)later_events
    (gateway_live(Callstate(Internal helper)arguments continuation final)final_world)->
  exists(receipt:gateway_spawn_birth_receipt resources births world next engine_bytes[engine_bytes]
    [spawn_path_bytes;spawn_locale_bytes]plan settings),
    result=Vint Int.zero /\
    Mem.load Mint32 after(spawn_child_block blocks)0=
      Some(Vint(Int.repr(gateway_child_pid(gateway_spawned_birth _ _ _ _ _ _ _ _ _ receipt)))) /\
    gateway_caller_family native stable readonly(exchange_selected_block environment)reference owner after next /\
    gateway_pair_cells after data Ptrofs.zero data_left data_right /\
    gateway_pair_cells after control Ptrofs.zero control_left control_right /\
    (forall fd entry,gateway_owned_descriptor(resources world)fd entry->gateway_owned_descriptor(resources next)fd entry) /\
    gateway_child_history_retained(births world)(births next).
Proof.
  intros ALLOC STORAGE INITIAL LOADED ENGINE PATH LOCALE OPERATION LATER.
  destruct(gateway_actual_selected_spawn backend io native stable discipline resources ipc builders genuine footprint births executed
    sdk process readonly reference owner environment data control actions attributes blocks symbols data_identity control_identity
    data_left data_right control_left control_right plan settings before world result after next observed engine_bytes
    STORAGE INITIAL LOADED ENGINE PATH LOCALE OPERATION)
    as(NORMAL&GENUINE&VALID&BUILDERS&IO&FAMILY&DATA_CELLS&CONTROL_CELLS&OWNED&HISTORY&status&created&RESULT&CHILD).
  subst result.
  pose proof(actual_spawn_before_internal_success backend allocation_before allocated environment temporaries after next status
    later_events helper arguments continuation final final_world ALLOC LATER)as ZERO;subst status.
  destruct(CHILD eq_refl)as[receipt[CREATED PID]].
  exists receipt;split;[reflexivity|]. split;[exact PID|]. split;[exact FAMILY|].
  split;[exact DATA_CELLS|]. split;[exact CONTROL_CELLS|]. split;assumption.
Qed.
