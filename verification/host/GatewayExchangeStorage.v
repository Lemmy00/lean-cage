(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Real exchange allocation produces every local launch-storage
   input. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayThreadRuntime GatewayCallerBuffers GatewayCallerFamily GatewayLocalRuntime
  GatewayStackAllocation GatewayExchangeEntry GatewayExchangeScope GatewayExchangeSetup GatewaySpawnABI GatewayBuilderHistory
  GatewaySpawnVectors GatewaySpawnVectorMemory GatewaySpawnVectorStores GatewayVectorCells GatewayCancellationInputs.
Import ListNotations.

Record gateway_exchange_storage {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    readonly memory world environment data control actions attributes blocks symbols:Prop:={
  exchange_storage_data:environment!_pair=Some(data,tarray tint 2);
  exchange_storage_control:environment!_control=Some(control,tarray tint 2);
  exchange_storage_actions:environment!_actions=Some(actions,gateway_actions_type);
  exchange_storage_attributes:environment!_attributes=Some(attributes,gateway_attributes_type);
  exchange_storage_data_control:data<>control;
  exchange_storage_actions_data:actions<>data;
  exchange_storage_actions_control:actions<>control;
  exchange_storage_attributes_data:attributes<>data;
  exchange_storage_attributes_control:attributes<>control;
  exchange_storage_headers:actions<>attributes;
  exchange_storage_data_readonly:forall position,~readonly data position;
  exchange_storage_control_readonly:forall position,~readonly control position;
  exchange_storage_actions_readonly:forall position,~readonly actions position;
  exchange_storage_attributes_readonly:forall position,~readonly attributes position;
  exchange_storage_data_range:Mem.range_perm memory data 0 8 Cur Freeable;
  exchange_storage_control_range:Mem.range_perm memory control 0 8 Cur Freeable;
  exchange_storage_actions_range:Mem.range_perm memory actions 0 80 Cur Freeable;
  exchange_storage_attributes_range:Mem.range_perm memory attributes 0 336 Cur Freeable;
  exchange_storage_locations:gateway_spawn_vector_locations(Clight.globalenv prog)environment blocks symbols;
  exchange_storage_vectors_distinct:gateway_spawn_blocks_distinct blocks;
  exchange_storage_cells:forall cell,In cell(gateway_spawn_cell_plan blocks symbols)->
    exchange_selected_block environment(vector_cell_block cell) /\
    vector_cell_block cell<>data /\vector_cell_block cell<>control /\
    vector_cell_block cell<>actions /\vector_cell_block cell<>attributes /\
    (forall position,~readonly(vector_cell_block cell)position);
  exchange_storage_access:Forall(gateway_vector_writable memory)(gateway_spawn_cell_plan blocks symbols);
  exchange_storage_family:gateway_caller_family native stable readonly(exchange_selected_block environment)memory world memory world;
  exchange_storage_sdk_roots:gateway_builder_headers native actions attributes memory world
}.

Theorem actual_exchange_storage_inputs {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    allocation_before allocated environment world readonly:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  gateway_native_environment native world allocated environment->
  gateway_caller_readonly native stable readonly allocation_before world->
  exists data control actions attributes blocks symbols,
    gateway_exchange_storage native stable readonly allocated world environment data control actions attributes blocks symbols.
Proof.
  intros ALLOC NATIVE READONLY.
  pose proof(actual_exchange_allocations(Clight.globalenv prog)allocation_before environment allocated ALLOC)as STORAGE.
  pose proof STORAGE as STORAGE_COPY;destruct STORAGE_COPY as[BUFFERS[[LIVE DISTINCT]FRAME]].
  destruct(BUFFERS _pair(tarray tint 2)ltac:(cbn;auto 14))as[data[DATA[FRESH_DATA DATA_RANGE]]].
  destruct(BUFFERS _control(tarray tint 2)ltac:(cbn;auto 14))as[control[CONTROL[FRESH_CONTROL CONTROL_RANGE]]].
  destruct(BUFFERS _actions gateway_actions_type ltac:(cbn;auto 14))as[actions[ACTIONS[FRESH_ACTIONS ACTIONS_RANGE]]].
  destruct(BUFFERS _attributes gateway_attributes_type ltac:(cbn;auto 14))as[attributes[ATTRIBUTES[FRESH_ATTRIBUTES ATTRIBUTES_RANGE]]].
  destruct(actual_exchange_entry_owns_spawn_vectors(Clight.globalenv prog)allocation_before environment allocated STORAGE)
    as(child&arguments&variables&CHILD&ARGUMENTS&VARIABLES&CHILD_ARGUMENTS&CHILD_VARIABLES&ARGUMENTS_VARIABLES&
      CHILD_RANGE&ARGUMENTS_RANGE&VARIABLES_RANGE).
  set(blocks:={|spawn_child_block:=child;spawn_arguments_block:=arguments;spawn_environment_block:=variables|}).
  assert(ENGINE_DEFINITION:exists variable,(prog_defmap prog)!_host_engine=Some(Gvar variable))
    by(eexists;vm_compute;reflexivity).
  assert(PATH_DEFINITION:exists variable,(prog_defmap prog)!(spawn_vector_literal 3)=Some(Gvar variable))
    by(eexists;vm_compute;reflexivity).
  assert(LOCALE_DEFINITION:exists variable,(prog_defmap prog)!(spawn_vector_literal 4)=Some(Gvar variable))
    by(eexists;vm_compute;reflexivity).
  destruct ENGINE_DEFINITION as[engine_variable ENGINE_DEFINITION].
  destruct PATH_DEFINITION as[path_variable PATH_DEFINITION].
  destruct LOCALE_DEFINITION as[locale_variable LOCALE_DEFINITION].
  destruct(gateway_actual_variable_binding _host_engine engine_variable ENGINE_DEFINITION)as[engine[ENGINE ENGINE_DATA]].
  destruct(gateway_actual_variable_binding(spawn_vector_literal 3)path_variable PATH_DEFINITION)as[path[PATH PATH_DATA]].
  destruct(gateway_actual_variable_binding(spawn_vector_literal 4)locale_variable LOCALE_DEFINITION)as[locale[LOCALE LOCALE_DATA]].
  set(symbols:={|spawn_engine_symbol:=engine;spawn_path_symbol:=path;spawn_locale_symbol:=locale|}).
  assert(FRESH_READONLY:forall object,~Mem.valid_block allocation_before object->forall position,~readonly object position).
  { intros object FRESH position HERE;exact(FRESH(proj1(READONLY object position HERE))). }
  assert(LOCAL_READONLY:forall identifier ty object,
    In(identifier,ty)(fn_vars f_host_exchange)->environment!identifier=Some(object,ty)->forall position,~readonly object position).
  { intros identifier ty object MEMBER LOOK;destruct(BUFFERS identifier ty MEMBER)as[actual[ACTUAL[FRESH RANGE]]].
    rewrite LOOK in ACTUAL;inversion ACTUAL;subst actual;apply FRESH_READONLY;exact FRESH. }
  assert(VECTOR_LOCAL:forall cell,In cell(gateway_spawn_cell_plan blocks symbols)->
    exists identifier ty,environment!identifier=Some(vector_cell_block cell,ty) /\
      In(identifier,ty)(fn_vars f_host_exchange) /\identifier<>_pair /\identifier<>_control /\
      identifier<>_actions /\identifier<>_attributes).
  { intros cell MEMBER;cbn[gateway_spawn_cell_plan]in MEMBER.
    repeat destruct MEMBER as[SAME|MEMBER];try contradiction;subst cell;
      cbn[blocks spawn_pointer_cell];
      first[solve[exists _child,tint;split;[exact CHILD|];split;[cbn;auto 14|];repeat split;discriminate]|
        solve[exists _arguments,(tarray(tptr tschar)2);split;[exact ARGUMENTS|];split;[cbn;auto 14|];repeat split;discriminate]|
        solve[exists _environment,(tarray(tptr tschar)3);split;[exact VARIABLES|];split;[cbn;auto 14|];repeat split;discriminate]]. }

  exists data,control,actions,attributes,blocks,symbols;constructor;try assumption.
  - eapply DISTINCT;[exact DATA|exact CONTROL|discriminate].
  - eapply DISTINCT;[exact ACTIONS|exact DATA|discriminate].
  - eapply DISTINCT;[exact ACTIONS|exact CONTROL|discriminate].
  - eapply DISTINCT;[exact ATTRIBUTES|exact DATA|discriminate].
  - eapply DISTINCT;[exact ATTRIBUTES|exact CONTROL|discriminate].
  - eapply DISTINCT;[exact ACTIONS|exact ATTRIBUTES|discriminate].
  - apply FRESH_READONLY;exact FRESH_DATA.
  - apply FRESH_READONLY;exact FRESH_CONTROL.
  - apply FRESH_READONLY;exact FRESH_ACTIONS.
  - apply FRESH_READONLY;exact FRESH_ATTRIBUTES.
  - constructor;try assumption.
    + eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate].
    + eapply actual_exchange_setup_unshadowed;[exact ALLOC|vm_compute;intuition discriminate].
    + eapply actual_exchange_setup_unshadowed;[exact ALLOC|vm_compute;intuition discriminate].
  - split;[exact CHILD_ARGUMENTS|]. split;assumption.
  - intros cell MEMBER;destruct(VECTOR_LOCAL cell MEMBER)as[identifier[ty[LOOK[LOCAL[PAIR[CTRL[ACT ATTR]]]]]]].
    split;[exists identifier,ty;exact LOOK|]. split;[eapply DISTINCT;[exact LOOK|exact DATA|exact PAIR]|].
    split;[eapply DISTINCT;[exact LOOK|exact CONTROL|exact CTRL]|].
    split;[eapply DISTINCT;[exact LOOK|exact ACTIONS|exact ACT]|].
    split;[eapply DISTINCT;[exact LOOK|exact ATTRIBUTES|exact ATTR]|].
    eapply LOCAL_READONLY;[exact LOCAL|exact LOOK].
  - apply gateway_spawn_vectors_writable;assumption.
  - eapply actual_exchange_native_family;[exact STORAGE|exact NATIVE|exact READONLY].
  - intros object MEMBER;cbn in MEMBER;destruct MEMBER as[SAME|[SAME|IMPOSSIBLE]];try contradiction;subst object.
    + exact(NATIVE _ _ _ ACTIONS).
    + exact(NATIVE _ _ _ ATTRIBUTES).
Qed.
