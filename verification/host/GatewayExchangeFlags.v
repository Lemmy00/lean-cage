(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original launch passes actual flag calls before SDK initialization. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime
  GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewayPairContext GatewayExchangeSetup GatewayExchangeFlagContext
  GatewayExchangeFlagSource GatewayExchangeFlagReturn GatewayLaunchPaths GatewayLaunchMemory GatewayLaunchSDK GatewayMemoryPrefixes.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_flags_temps flags right temporaries:=exchange_set_flags_return Int.zero
  (exchange_set_flags_temps flags right(PTree.set _t'99(Vint(Int.repr right))temporaries)).

Section Flags.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state)
    (data_identity control_identity:gateway_pair_identity ipc)(data control:block)(data_left data_right control_left control_right:Z).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control).
Local Definition property:=gateway_flag_context native stable discipline resources ipc readonly selected reference owner original
  data_identity control_identity data control data_left data_right control_left control_right.

Local Lemma property_closed left_mode right_mode:gateway_ambient_closed backend(property left_mode right_mode).
Proof.
  intros before world after next READY INTERFERENCE.
  eapply gateway_flag_context_ambient with(io:=io)(thread_errno:=thread_errno);eassumption.
Qed.
Local Lemma property_cells left_mode right_mode before world:
  property left_mode right_mode before world->gateway_pair_cells before data Ptrofs.zero data_left data_right.
Proof. intros[_[_[_[_[_[_[CELLS REST]]]]]]];exact CELLS. Qed.

Theorem actual_exchange_flags_before_sdk allocation_before allocated environment temporaries before world events
    arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_pair=Some(data,tarray tint 2)->property true true before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists flags prefix suffix sdk_before sdk_world,
    0<=Int.signed flags /\events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_setup_after 6)Kstop environment
        (exchange_flags_temps flags data_right temporaries)sdk_before)sdk_world) /\
    property true false sdk_before sdk_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 6)Kstop environment
        (exchange_flags_temps flags data_right temporaries)sdk_before)sdk_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC ARRAY INITIAL RUN.
  set(get_temps:=PTree.set _t'99(Vint(Int.repr data_right))temporaries).
  set(target:=fun(source:Clight.state)(current:World)=>exists flags memory,
    0<=Int.signed flags /\source=State f_host_exchange(exchange_setup_after 6)Kstop environment
      (exchange_flags_temps flags data_right temporaries)memory /\property true false memory current).
  assert(TRUE_CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(GET_PATH:gateway_launch_path backend target(property true true)
    (Callstate(gateway_spawn_signature gateway_fcntl_api)
      [Vint(Int.repr data_right);Vint(Int.repr 3);Vint Int.zero](exchange_get_flags_cont environment get_temps)before)).
  { eapply gateway_launch_sdk_operation;[discriminate|apply property_closed|].
    intros called current result changed later observed READY OPERATION.
    destruct(gateway_actual_get_flags_context backend io native stable discipline resources ipc descriptors
      readonly selected reference owner original data_identity control_identity data control data_left data_right control_left control_right
      DATA_SELECTED CONTROL_SELECTED called current result changed later observed READY OPERATION)
      as[POST[IO[FAILED|[flags[RESULT NONNEGATIVE]]]]].
    - subst result;exists(property true true);split;[exact POST|].
      eapply actual_exchange_after_get_script;
        [apply property_closed|exact ALLOC|exact ARRAY|apply property_cells|].
      intro IMPOSSIBLE;change(0<= -1)in IMPOSSIBLE;lia.
    - subst result;exists(property true true);split;[exact POST|].
      eapply actual_exchange_after_get_script;
        [apply property_closed|exact ALLOC|exact ARRAY|apply property_cells|].
      intro VALID_FLAGS;eapply gateway_launch_sdk_operation;[discriminate|apply property_closed|].
      intros sent sending set_result after_set set_world set_observed SET_READY SET_OPERATION.
      destruct(gateway_actual_set_flags_context backend io native stable discipline resources ipc descriptors
        readonly selected reference owner original data_identity control_identity data control data_left data_right control_left control_right
        DATA_SELECTED CONTROL_SELECTED flags sent sending set_result after_set set_world set_observed SET_READY SET_OPERATION)
        as[SET_IO[FAILED|[ZERO BLOCKING]]].
      + subst set_result;exists(fun _ _=>True);split;[exact I|].
        eapply actual_exchange_after_set_script;[exact TRUE_CLOSED|exact ALLOC|right;reflexivity|].
        intro BAD;discriminate BAD.
      + subst set_result;exists(property true false);split;[exact BLOCKING|].
        eapply actual_exchange_after_set_script;[apply property_closed|exact ALLOC|left;reflexivity|].
        intro ZERO;apply gateway_launch_reached;intros memory final FINAL.
        exists flags,memory;split;[exact NONNEGATIVE|]. split;[reflexivity|exact FINAL]. }
  destruct(actual_gateway_spawn_binding gateway_fcntl_api)as[symbol[SYMBOL FUNCTION]].
  assert(UNSHADOWED:environment!_leancage_host_fcntl=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  pose proof(actual_exchange_get_flags_prefix backend(property true true)(property_closed true true)environment temporaries
    before data data_left data_right symbol ARRAY UNSHADOWED SYMBOL FUNCTION(property_cells true true))as GET_PREFIX.
  pose proof(gateway_launch_after_memory_prefix backend _ _ _ _ target GET_PREFIX GET_PATH)as SCRIPT.
  destruct(gateway_launch_prefix_cut backend target(property true true)
    (State f_host_exchange(exchange_setup_after 4)Kstop environment temporaries before)before world events
    arguments continuation after next SCRIPT INITIAL RUN)
    as(prefix&suffix&selected_state&selected_world&EVENTS&PREFIX&POINT&SUFFIX).
  destruct POINT as[flags[memory[NONNEGATIVE[SOURCE FINAL]]]];subst selected_state.
  exists flags,prefix,suffix,memory,selected_world.
  split;[exact NONNEGATIVE|]. split;[exact EVENTS|]. split;[exact PREFIX|]. split;assumption.
Qed.
End Flags.
