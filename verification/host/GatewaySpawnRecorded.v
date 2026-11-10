(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The selected real spawn records its exact source-built plan and
   vectors. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI
  GatewaySpawnActions GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnProcess GatewaySpawnCall GatewaySpawnInputCells
  GatewaySpawnVectors GatewaySpawnVectorMemory GatewaySpawnVectorValues GatewayVectorCells GatewayPairContext GatewaySDKInputs
  GatewaySDKContext GatewayExchangeStorage GatewayExchangeScope GatewayCallerFamily GatewayErrorRuntime.
Import ListNotations.

Theorem gateway_actual_selected_spawn {World Event}(backend:gateway_backend World Event)io native stable discipline resources ipc
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
  discipline None after next /\genuine after next /\gateway_resource_valid(resources next) /\
  builders next=builders world /\io observed=None /\
  gateway_caller_family native stable readonly(exchange_selected_block environment)reference owner after next /\
  gateway_pair_cells after data Ptrofs.zero data_left data_right /\
  gateway_pair_cells after control Ptrofs.zero control_left control_right /\
  (forall fd entry,gateway_owned_descriptor(resources world)fd entry->gateway_owned_descriptor(resources next)fd entry) /\
  gateway_child_history_retained(births world)(births next) /\
  exists status(created:option(gateway_spawn_birth_receipt resources births world next engine_bytes[engine_bytes]
    [spawn_path_bytes;spawn_locale_bytes]plan settings)),result=Vint status /\
    (status=Int.zero->exists receipt,created=Some receipt /\
      Mem.load Mint32 after(spawn_child_block blocks)0=
        Some(Vint(Int.repr(gateway_child_pid(gateway_spawned_birth _ _ _ _ _ _ _ _ _ receipt))))).
Proof.
  intros STORAGE INITIAL LOADED ENGINE PATH LOCALE OPERATION.
  destruct(gateway_spawn_child_slot backend io native stable discipline resources ipc builders genuine footprint sdk
    readonly reference owner environment data control actions attributes blocks symbols data_identity control_identity
    data_left data_right control_left control_right plan settings before world STORAGE INITIAL)
    as[NATIVE[POINTER[ACCESS OUTSIDE]]].
  destruct(gateway_spawn_vectors_from_cells before blocks symbols engine_bytes LOADED ENGINE PATH LOCALE)as[ARGUMENTS ENVIRONMENT].
  pose proof INITIAL as INITIAL_COPY;destruct INITIAL_COPY as[FLAGS[GENUINE[ACT ATTR]]].
  destruct(gateway_posix_spawn_operation backend io native stable discipline resources builders genuine footprint births executed process before world(spawn_child_block blocks)Ptrofs.zero
    (Vptr(spawn_engine_symbol symbols)Ptrofs.zero)engine_bytes(Vptr actions Ptrofs.zero)plan(Vptr attributes Ptrofs.zero)settings
    (Vptr(spawn_arguments_block blocks)Ptrofs.zero)[engine_bytes](Vptr(spawn_environment_block blocks)Ptrofs.zero)
    [spawn_path_bytes;spawn_locale_bytes]result after next observed(proj1 FLAGS)GENUINE(proj1(proj2(proj2 FLAGS)))NATIVE POINTER ACCESS
    OUTSIDE ACT ATTR ENGINE ARGUMENTS ENVIRONMENT OPERATION)
    as(NORMAL&AFTER_GENUINE&VALID&BUILDERS&RETAINED&PERMISSIONS&FRAME&RESOURCES&HISTORY&IO&status&created&RESULT&CHILD&NEW).
  set(cell:={|vector_cell_block:=spawn_child_block blocks;vector_cell_offset:=0;vector_cell_chunk:=Mint32;
    vector_cell_value:=Vint Int.zero|}).
  assert(MEMBER:In cell(gateway_spawn_cell_plan blocks symbols))by(left;reflexivity).
  destruct(exchange_storage_cells native stable readonly reference owner environment data control actions attributes blocks symbols
    STORAGE cell MEMBER)as[SELECTED[AWAY_DATA[AWAY_CONTROL[AWAY_ACTIONS[AWAY_ATTRIBUTES READONLY]]]]].
  change(spawn_child_block blocks<>data)in AWAY_DATA.
  change(spawn_child_block blocks<>control)in AWAY_CONTROL.
  split;[exact NORMAL|]. split;[exact AFTER_GENUINE|]. split;[exact VALID|]. split;[exact BUILDERS|]. split;[exact IO|]. split.
  - eapply gateway_caller_family_output;[exact(proj1(proj2 FLAGS))|exact READONLY|exact RETAINED|exact PERMISSIONS|exact FRAME].
  - destruct FLAGS as(SIDE&FAMILY&INITIAL_VALID&DLEASE&CLEASE&MODES&DATA_CELLS&CONTROL_CELLS&ORIGINAL).
    split.
    + eapply gateway_pair_cells_unchanged;[exact DATA_CELLS|].
      eapply gateway_native_frame_restrict;[exact FRAME| |].
      * intros object position[SAME INSIDE];subst object;left.
        exact(proj1(proj2(FAMILY data ltac:(exists _pair,(Ctypesdefs.tarray Ctypesdefs.tint 2);exact(exchange_storage_data _ _ _ _ _ _ _ _ _ _ _ _ STORAGE))))).
      * intros object position[SAME INSIDE][PID WRITTEN];congruence.
    + split.
      * eapply gateway_pair_cells_unchanged;[exact CONTROL_CELLS|].
        eapply gateway_native_frame_restrict;[exact FRAME| |].
        -- intros object position[SAME INSIDE];subst object;left.
           exact(proj1(proj2(FAMILY control ltac:(exists _control,(Ctypesdefs.tarray Ctypesdefs.tint 2);exact(exchange_storage_control _ _ _ _ _ _ _ _ _ _ _ _ STORAGE))))).
        -- intros object position[SAME INSIDE][PID WRITTEN];congruence.
      * split;[intros fd entry OWNED;apply(proj1 RESOURCES);[exact OWNED|tauto]|].
        split;[exact HISTORY|]. exists status,created;split;[exact RESULT|exact CHILD].
Qed.
