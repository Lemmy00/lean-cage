(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The selected spawn follows this invocation's actual six successful
   edits. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewaySpawnActions GatewaySpawnDescriptors
  GatewayPairContext GatewaySDKInputs GatewaySDKRuntimeContext GatewaySDKEditSource GatewaySDKEditReturn
  GatewaySDKEditEffects GatewaySDKVectors GatewaySDKFailurePaths GatewayExchangeSetup GatewayFramedRuntime
  GatewayLaunchPaths GatewayLaunchMemory GatewayLaunchSDK GatewayLaunchPre GatewaySpawnVectorMemory
  GatewaySpawnVectorPrefix GatewaySpawnVectorStores GatewaySpawnVectors GatewaySpawnCall GatewayMemoryPrefixes GatewayVectorCells.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_sdk_temps_exact data_right control_right temporaries:=
  sdk_edit_return_temps gateway_edit_closefrom Int.zero data_right control_right
    (sdk_edit_return_temps gateway_edit_cancellation Int.zero data_right control_right
      (sdk_edit_return_temps gateway_edit_output Int.zero data_right control_right
        (sdk_edit_return_temps gateway_edit_input Int.zero data_right control_right
          (sdk_edit_return_temps gateway_edit_flags Int.zero data_right control_right
            (sdk_edit_return_temps gateway_edit_group Int.zero data_right control_right temporaries))))).
Definition exchange_sdk_plan data_right control_right:=
  [gateway_spawn_dup data_right 0;gateway_spawn_dup data_right 1;
   gateway_spawn_dup control_right 3;gateway_spawn_closefrom 4].
Definition exchange_sdk_attributes:gateway_spawn_attributes:=
  {|gateway_attribute_flags:=Int.repr 2;gateway_attribute_group:=Int.zero|}.

Section Setup.
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
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(ACTIONS_SELECTED:selected actions)
    (ATTRIBUTES_SELECTED:selected attributes)(ACTIONS_DATA:actions<>data)(ACTIONS_CONTROL:actions<>control)
    (ATTRIBUTES_DATA:attributes<>data)(ATTRIBUTES_CONTROL:attributes<>control)
    (ACTIONS_READONLY:forall position,~readonly actions position)(ATTRIBUTES_READONLY:forall position,~readonly attributes position)
    (ACTIONS_RANGE:Mem.range_perm reference actions 0 80 Cur Freeable)
    (ATTRIBUTES_RANGE:Mem.range_perm reference attributes 0 336 Cur Freeable).
Variables(allocation_before allocated:mem)(environment:env).
Hypotheses(ALLOC:alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated)
    (ACTIONS:environment!_actions=Some(actions,gateway_actions_type))
    (ATTRIBUTES:environment!_attributes=Some(attributes,gateway_attributes_type))
    (DATA:environment!_pair=Some(data,tarray tint 2))(CONTROL:environment!_control=Some(control,tarray tint 2)).
Variables(blocks:gateway_spawn_vector_blocks)(symbols:gateway_spawn_vector_symbols).
Hypotheses(LOCATIONS:gateway_spawn_vector_locations(Clight.globalenv prog)environment blocks symbols)
    (DISTINCT:gateway_spawn_blocks_distinct blocks)
    (CELLS:forall cell,In cell(gateway_spawn_cell_plan blocks symbols)->
      selected(vector_cell_block cell) /\vector_cell_block cell<>data /\vector_cell_block cell<>control /\
      vector_cell_block cell<>actions /\vector_cell_block cell<>attributes /\
      (forall position,~readonly(vector_cell_block cell)position))
    (ACCESS:Forall(gateway_vector_writable reference)(gateway_spawn_cell_plan blocks symbols)).
Local Definition context plan settings:=gateway_sdk_context native stable discipline resources ipc readonly selected reference owner original
  data_identity control_identity data control data_left data_right control_left control_right builders genuine
  (Some(Vptr actions Ptrofs.zero,plan))(Some(Vptr attributes Ptrofs.zero,settings)).

Local Lemma context_closed plan settings:gateway_ambient_closed backend(context plan settings).
Proof. eapply gateway_sdk_context_ambient with(io:=io)(thread_errno:=thread_errno);eassumption. Qed.

Local Lemma context_vector_ambient plan settings before world after next:
  context plan settings before world->gateway_interference backend before world after next->
  context plan settings after next /\Mem.unchanged_on(gateway_vector_span(gateway_spawn_cell_plan blocks symbols))before after.
Proof.
  eapply gateway_sdk_vectors_ambient with(io:=io)(thread_errno:=thread_errno)(footprint:=footprint);eassumption.
Qed.
Local Lemma context_vector_store plan settings before world after cell:
  context plan settings before world->In cell(gateway_spawn_cell_plan blocks symbols)->
  Mem.store(vector_cell_chunk cell)before(vector_cell_block cell)(vector_cell_offset cell)(vector_cell_value cell)=Some after->
  context plan settings after world.
Proof.
  eapply gateway_sdk_vectors_store with(io:=io)(thread_errno:=thread_errno)(footprint:=footprint);eassumption.
Qed.

Local Lemma failed_edit_path target edit plan settings temporaries memory status:
  temporaries!_setup=Some(Vint status)->Int.eq status Int.zero=false->
  gateway_launch_path backend target(context plan settings)
    (State f_host_exchange(sdk_edit_after edit)Kstop environment temporaries memory).
Proof.
  intros SETUP NONZERO.
  eapply gateway_launch_pre.
  - eapply actual_sdk_failed_edit_path with(blocks:=blocks)(symbols:=symbols)(base:=context plan settings)
      (word:=status);[exact LOCATIONS|exact DISTINCT|apply context_vector_ambient|apply context_vector_store|
        exact ALLOC|exact SETUP|exact NONZERO].
  - apply context_closed.
  - intros before world READY;split;[exact READY|]. split;[|constructor].
    eapply gateway_sdk_vector_access;[exact CELLS|exact READY|exact ACCESS].
Qed.

Local Lemma edit_path target edit plan settings temporaries memory:
  temporaries!_setup=Some(Vint Int.zero)->
  (forall after,gateway_launch_path backend target
    (context(sdk_edit_plan edit Int.zero data_right control_right plan)(sdk_edit_settings edit Int.zero settings))
    (State f_host_exchange(sdk_edit_after edit)Kstop environment
      (sdk_edit_return_temps edit Int.zero data_right control_right temporaries)after))->
  gateway_launch_path backend target(context plan settings)
    (State f_host_exchange(sdk_edit_start edit)Kstop environment temporaries memory).
Proof.
  intros SETUP SUCCESS.
  eapply gateway_launch_after_memory_prefix.
  - eapply actual_sdk_edit_prefix with(edit:=edit)(data_left:=data_left)(data_right:=data_right)
      (control_left:=control_left)(control_right:=control_right);
      [apply context_closed|exact ALLOC|exact ACTIONS|exact ATTRIBUTES|exact DATA|exact CONTROL|exact SETUP|].
    intros before world READY.
    destruct(proj1 READY)as(SIDE&FAMILY&VALID&DLEASE&CLEASE&MODES&DATA_CELLS&CONTROL_CELLS&ORIGINAL).
    split;assumption.
  - eapply gateway_launch_sdk_operation;[destruct edit;discriminate|apply context_closed|].
    intros before world result after next observed READY OPERATION.
    destruct(actual_sdk_edit_effect backend io native stable discipline resources ipc builders genuine footprint sdk
      readonly selected reference owner original data_identity control_identity data control data_left data_right
      control_left control_right actions attributes DATA_SELECTED CONTROL_SELECTED ACTIONS_SELECTED ATTRIBUTES_SELECTED
      ACTIONS_DATA ACTIONS_CONTROL ATTRIBUTES_DATA ATTRIBUTES_CONTROL ACTIONS_READONLY ATTRIBUTES_READONLY
      ACTIONS_RANGE ATTRIBUTES_RANGE edit plan settings before world result after next observed READY OPERATION)
      as[status[RESULT[QUIET POST]]].
    subst result;exists(context(sdk_edit_plan edit status data_right control_right plan)(sdk_edit_settings edit status settings));
      split;[exact POST|].
    eapply actual_sdk_edit_return_path;[apply context_closed|].
    destruct(Int.eq status Int.zero)eqn:ZERO.
    + apply Int.same_if_eq in ZERO;subst status;apply SUCCESS.
    + eapply failed_edit_path;[apply PTree.gss|exact ZERO].
Qed.

Theorem actual_exchange_sdk_before_vectors temporaries before world events arguments continuation after next:
  temporaries!_setup=Some(Vint Int.zero)->context [] gateway_default_attributes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 10)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 10)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_setup_after 16)Kstop environment
        (exchange_sdk_temps_exact data_right control_right temporaries)memory)current) /\
    context(exchange_sdk_plan data_right control_right)exchange_sdk_attributes memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 16)Kstop environment
        (exchange_sdk_temps_exact data_right control_right temporaries)memory)current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros SETUP INITIAL RUN.
  set(target:=fun(source:Clight.state)(current:World)=>exists memory,
    source=State f_host_exchange(exchange_setup_after 16)Kstop environment
      (exchange_sdk_temps_exact data_right control_right temporaries)memory /\
    context(exchange_sdk_plan data_right control_right)exchange_sdk_attributes memory current).
  assert(SCRIPT:gateway_launch_path backend target(context [] gateway_default_attributes)
    (State f_host_exchange(exchange_setup_after 10)Kstop environment temporaries before)).
  { eapply edit_path with(edit:=gateway_edit_group);[exact SETUP|intro].
    eapply edit_path with(edit:=gateway_edit_flags);[apply PTree.gss|intro].
    eapply edit_path with(edit:=gateway_edit_input);[apply PTree.gss|intro].
    eapply edit_path with(edit:=gateway_edit_output);[apply PTree.gss|intro].
    eapply edit_path with(edit:=gateway_edit_cancellation);[apply PTree.gss|intro].
    eapply edit_path with(edit:=gateway_edit_closefrom);[apply PTree.gss|intro].
    apply gateway_launch_reached;intros memory current READY;exists memory;split;[reflexivity|exact READY]. }
  destruct(gateway_launch_prefix_cut backend target(context [] gateway_default_attributes)
    (State f_host_exchange(exchange_setup_after 10)Kstop environment temporaries before)before world events
    arguments continuation after next SCRIPT INITIAL RUN)
    as(prefix&suffix&point&current&EVENTS&PREFIX&POINT&SUFFIX).
  destruct POINT as[memory[SOURCE FINAL]];subst point.
  exists prefix,suffix,memory,current;split;[exact EVENTS|]. split;[exact PREFIX|]. split;assumption.
Qed.

Theorem actual_exchange_sdk_selected_call temporaries before world events arguments continuation after next:
  temporaries!_setup=Some(Vint Int.zero)->context [] gateway_default_attributes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 10)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 10)Kstop environment temporaries before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
        (gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment(exchange_sdk_temps_exact data_right control_right temporaries)Kstop)memory)current) /\
    context(exchange_sdk_plan data_right control_right)exchange_sdk_attributes memory current /\
    Forall(gateway_vector_loaded memory)(gateway_spawn_cell_plan blocks symbols) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)
        (gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment(exchange_sdk_temps_exact data_right control_right temporaries)Kstop)memory)current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros SETUP INITIAL RUN.
  destruct(actual_exchange_sdk_before_vectors temporaries before world events arguments continuation after next SETUP INITIAL RUN)
    as(setup_prefix&rest&vector_before&vector_world&EVENTS1&SETUP_RUN&VECTOR_READY&TAIL).
  set(base:=context(exchange_sdk_plan data_right control_right)exchange_sdk_attributes).
  set(temps:=exchange_sdk_temps_exact data_right control_right temporaries).
  pose proof(context_vector_ambient(exchange_sdk_plan data_right control_right)exchange_sdk_attributes)as AMBIENT.
  pose proof(context_vector_store(exchange_sdk_plan data_right control_right)exchange_sdk_attributes)as STORES.
  pose proof(gateway_spawn_vectors_script backend(Clight.globalenv prog)environment temps blocks symbols base
    LOCATIONS DISTINCT AMBIENT STORES Kstop vector_before)as VECTORS.
  destruct(actual_gateway_spawn_binding gateway_posix_spawn_api)as[symbol[SYMBOL FUNCTION]].
  assert(CALL:gateway_memory_prefix backend(Clight.globalenv prog)
    (Callstate(gateway_spawn_signature gateway_posix_spawn_api)(gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment temps Kstop)vector_before)
    (gateway_spawn_vector_progress blocks symbols base 6)(gateway_spawn_vector_progress blocks symbols base 6)
    (State f_host_exchange(spawn_vector_after 6)Kstop environment temps vector_before)).
  { eapply actual_spawn_selected_script;
      [exact(gateway_spawn_progress_ambient backend blocks symbols base AMBIENT 6)|exact LOCATIONS|
       exact ACTIONS|exact ATTRIBUTES| |exact SYMBOL|exact FUNCTION|apply PTree.gss].
    eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  pose proof(gateway_memory_prefix_compose backend(Clight.globalenv prog)_ _ _ _ _ _ VECTORS CALL)as SCRIPT.
  assert(WRITABLE:Forall(gateway_vector_writable vector_before)(gateway_spawn_cell_plan blocks symbols)).
  { eapply gateway_sdk_vector_access;[exact CELLS|exact VECTOR_READY|exact ACCESS]. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ vector_before vector_world rest
    (Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next SCRIPT I
    ltac:(split;[exact VECTOR_READY|split;[exact WRITABLE|constructor]])TAIL)
    as(vector_prefix&suffix&memory&current&EVENTS2&QUIET&VECTOR_RUN&[FINAL[ACCESS_FINAL LOADED]]&SUFFIX).
  exists(setup_prefix++vector_prefix),suffix,memory,current;split.
  - rewrite EVENTS1,EVENTS2,app_assoc;reflexivity.
  - split;[eapply gateway_steps_append;[exact SETUP_RUN|exact VECTOR_RUN]|].
    split;[exact FINAL|]. split;[exact LOADED|exact SUFFIX].
Qed.
End Setup.
