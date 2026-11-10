(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The same first pair birth remains owned at the second source call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFramedRuntime GatewayReadonly
  GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewayPairContext
  GatewayPairHistory GatewayPairSource GatewayExchangeContext GatewayExchangeSetup GatewayExchangePairPaths
  GatewayExchangePairReturns GatewayExchangePairContext GatewayExchangePairCall GatewayLaunchQuiet.
Import ListNotations.

Section FirstPair.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state).
Local Definition exchange_context:=gateway_exchange_context native stable discipline resources readonly selected reference owner original.

Theorem actual_exchange_data_pair_before_control allocation_before allocated environment temporaries data control
    before world events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_control=Some(control,tarray tint 2)->
  (forall position,~readonly data position)->selected data->Mem.range_perm reference data 0 8 Cur Freeable->
  exchange_context before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr data Ptrofs.zero]
      (exchange_pair_cont exchange_data_stage environment temporaries)before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists pair_events between suffix returned_memory returned_world control_before control_world
    (identity:gateway_pair_identity ipc)left right,
    events=pair_events++between++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr data Ptrofs.zero]Kstop before)world)pair_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop returned_memory)returned_world) /\
    gateway_pair_birth_in_run backend resources ipc data before world pair_events returned_memory returned_world identity /\
    (4<=left)%Z /\(4<=right)%Z /\Forall gateway_quiet_event between /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(exchange_pair_cont exchange_data_stage environment temporaries)returned_memory)
        returned_world)between
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]
        (exchange_pair_cont exchange_control_stage environment(PTree.set _t'3(Vint Int.zero)temporaries))control_before)control_world) /\
    gateway_pair_context native discipline resources ipc identity data Ptrofs.zero left right control_before control_world /\
    exchange_context control_before control_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]
        (exchange_pair_cont exchange_control_stage environment(PTree.set _t'3(Vint Int.zero)temporaries))control_before)control_world)
      suffix(gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC CONTROL DISJOINT SELECTED PERMISSIONS INITIAL RUN.
  destruct(actual_exchange_pair_returns_zero_before_spawn backend exchange_data_stage environment temporaries data
    allocation_before allocated before world events arguments continuation after next ALLOC RUN)
    as(pair_events&caller_events&returned_memory&returned_world&EVENTS&PAIR&CALLER).
  destruct(actual_exchange_pair_preserves_context backend io native stable discipline thread_errno resources ipc thread descriptors
    readonly selected reference owner original data before world pair_events returned_memory returned_world
    DISJOINT SELECTED PERMISSIONS INITIAL PAIR)as(identity&left&right&LEFT&RIGHT&BIRTH&PAIR_CONTEXT&EXCHANGE).
  set(property:=fun memory current=>gateway_pair_context native discipline resources ipc identity data Ptrofs.zero left right
    memory current /\exchange_context memory current).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current changed later[PRIVATE CONTEXT]INTERFERENCE;split.
    - eapply gateway_pair_context_ambient;[exact thread|exact descriptors|exact PRIVATE|exact INTERFERENCE].
    - eapply gateway_exchange_context_ambient;[exact thread|exact descriptors|exact CONTEXT|exact INTERFERENCE]. }
  set(target:=exchange_control_pair_point property environment(PTree.set _t'3(Vint Int.zero)temporaries)control).
  assert(SCRIPT:gateway_quiet_launch_path backend target property
    (Returnstate(Vint Int.zero)(exchange_pair_cont exchange_data_stage environment temporaries)returned_memory)).
  { eapply actual_exchange_pair_return_script;[exact CLOSED|exact ALLOC|right;left;reflexivity|].
    intros ZERO;apply actual_exchange_control_pair_script with(allocation_before:=allocation_before)(allocated:=allocated);
      [exact CLOSED|exact ALLOC|exact CONTROL]. }
  destruct(gateway_quiet_launch_cut backend target property
    (Returnstate(Vint Int.zero)(exchange_pair_cont exchange_data_stage environment temporaries)returned_memory)
    returned_memory returned_world caller_events arguments continuation after next SCRIPT(conj PAIR_CONTEXT EXCHANGE)CALLER)
    as(between&suffix&control_source&control_world&CALLER_EVENTS&QUIET&BETWEEN&POINT&SUFFIX).
  destruct POINT as[control_before[SOURCE[PAIR_AFTER CONTEXT_AFTER]]];subst control_source.
  exists pair_events,between,suffix,returned_memory,returned_world,control_before,control_world,identity,left,right.
  split;[rewrite EVENTS,CALLER_EVENTS;reflexivity|]. split;[exact PAIR|]. split;[exact BIRTH|].
  split;[exact LEFT|]. split;[exact RIGHT|]. split;[exact QUIET|]. split;[exact BETWEEN|].
  split;[exact PAIR_AFTER|]. split;assumption.
Qed.
End FirstPair.
