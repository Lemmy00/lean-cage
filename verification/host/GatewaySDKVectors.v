(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Actual vector stores preserve this invocation's SDK and IPC
   state. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnABI GatewaySpawnActions GatewaySpawnFrames GatewaySpawnRuntime GatewaySpawnResources
  GatewayPairContext GatewayCallerFamily GatewayCallerBuffers GatewaySDKInputs GatewaySDKRuntimeContext
  GatewayVectorCells GatewaySpawnVectorMemory GatewaySpawnVectorPrefix GatewayFramedRuntime.
Import ListNotations.

Section Vectors.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop)
    (builders:World->gateway_spawn_builders)(genuine:mem->World->Prop)(footprint:World->block->Z->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)
    (original:gateway_resource_state)(data_identity control_identity:gateway_pair_identity ipc)
    (data control:block)(data_left data_right control_left control_right:Z)(actions attributes:block).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control).
Local Definition context plan settings:=gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original
  data_identity control_identity data control data_left data_right control_left control_right builders genuine
  (Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings)).

Theorem gateway_sdk_context_store plan settings before world after object position chunk value:
  context plan settings before world->selected object->object<>data->object<>control->
  object<>actions->object<>attributes->(forall query,~readonly object query)->
  Mem.store chunk before object position value=Some after->context plan settings after world.
Proof.
  intros[FLAGS[GENUINE[ACT ATTR]]]SELECTED AWAY_DATA AWAY_CONTROL AWAY_ACTIONS AWAY_ATTRIBUTES DISJOINT STORE.
  destruct FLAGS as[SIDE[FAMILY[VALID[DATA[CONTROL[MODES[DATA_CELLS[CONTROL_CELLS ORIGINAL]]]]]]]].
  assert(NATIVE:native world object)by(exact(proj1(proj2(FAMILY object SELECTED)))).
  split.
  - split;[eapply gateway_thread_native_store;[exact thread|exact SIDE|exact NATIVE|exact STORE]|]. split.
    + intros target INCLUDED;eapply gateway_caller_buffers_store;[exact(FAMILY target INCLUDED)|exact STORE|exact DISJOINT].
    + split;[exact VALID|]. split;[exact DATA|]. split;[exact CONTROL|]. split;[exact MODES|]. split.
      * eapply gateway_pair_cells_unchanged;[exact DATA_CELLS|].
        eapply Mem.store_unchanged_on;[exact STORE|]. intros query RANGE[SAME INSIDE];congruence.
      * split.
        -- eapply gateway_pair_cells_unchanged;[exact CONTROL_CELLS|].
           eapply Mem.store_unchanged_on;[exact STORE|]. intros query RANGE[SAME INSIDE];congruence.
        -- exact ORIGINAL.
  - split.
    + eapply gateway_builder_store with(io:=io)(stable:=stable)(discipline:=discipline)(resources:=resources)
        (footprint:=footprint);[exact sdk|exact GENUINE|exact NATIVE| |exact STORE].
      split;intros offset recorded SAME;[rewrite ACT in SAME|rewrite ATTR in SAME];inversion SAME;congruence.
    + split;assumption.
Qed.

Variables(blocks:gateway_spawn_vector_blocks)(symbols:gateway_spawn_vector_symbols).
Hypothesis CELLS:forall cell,In cell(gateway_spawn_cell_plan blocks symbols)->
  selected(vector_cell_block cell) /\vector_cell_block cell<>data /\vector_cell_block cell<>control /\
  vector_cell_block cell<>actions /\vector_cell_block cell<>attributes /\
  (forall position,~readonly(vector_cell_block cell)position).

Theorem gateway_sdk_vectors_ambient plan settings before world after next:
  context plan settings before world->gateway_interference backend before world after next->
  context plan settings after next /\
  Mem.unchanged_on(gateway_vector_span(gateway_spawn_cell_plan blocks symbols))before after.
Proof.
  intros INITIAL INTERFERENCE;split.
  - eapply gateway_sdk_context_ambient with(io:=io)(thread_errno:=thread_errno);eassumption.
  - destruct(gateway_thread_ambient _ _ _ _ _ _ thread None before world after next(proj1(proj1 INITIAL))INTERFERENCE)
      as[NORMAL[ACCESS FRAME]].
    eapply Mem.unchanged_on_implies;[exact FRAME|]. intros object position[cell[MEMBER[SAME INSIDE]]];subst object.
    split;[left|tauto].
    exact(proj1(proj2((proj1(proj2(proj1 INITIAL)))(vector_cell_block cell)(proj1(CELLS cell MEMBER))))).
Qed.

Theorem gateway_sdk_vectors_store plan settings before world after cell:
  context plan settings before world->In cell(gateway_spawn_cell_plan blocks symbols)->
  Mem.store(vector_cell_chunk cell)before(vector_cell_block cell)(vector_cell_offset cell)(vector_cell_value cell)=Some after->
  context plan settings after world.
Proof.
  intros INITIAL MEMBER STORE;destruct(CELLS cell MEMBER)as[SELECTED[DATA[CONTROL[ACTIONS[ATTRIBUTES READONLY]]]]].
  eapply gateway_sdk_context_store;eassumption.
Qed.

Theorem gateway_sdk_vector_access plan settings memory world:
  context plan settings memory world->
  Forall(gateway_vector_writable reference)(gateway_spawn_cell_plan blocks symbols)->
  Forall(gateway_vector_writable memory)(gateway_spawn_cell_plan blocks symbols).
Proof.
  intros INITIAL ORIGINAL;rewrite Forall_forall in *;intros cell MEMBER.
  destruct(ORIGINAL cell MEMBER)as[PERMISSIONS ALIGN];split;[|exact ALIGN].
  destruct((proj1(proj2(proj1 INITIAL)))(vector_cell_block cell)(proj1(CELLS cell MEMBER)))
    as[LIVE[PRIVATE[READONLY[[FRAME CURRENT]REST]]]].
  intros position INSIDE;apply(proj1(CURRENT(vector_cell_block cell)(or_introl eq_refl)position Cur Writable)).
  apply PERMISSIONS;exact INSIDE.
Qed.
End Vectors.
