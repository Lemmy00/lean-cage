(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Both actual pair births reach the same caller's flag setup. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFramedRuntime GatewayReadonly
  GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewayPairContext
  GatewayPairHistory GatewayPairSource GatewayExchangeContext GatewayExchangeSetup GatewayExchangePairPaths
  GatewayExchangePairReturns GatewayExchangePairContext GatewayExchangeSecondContext GatewayLaunchQuiet.
Import ListNotations.

Section SecondPair.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state).
Local Definition exchange_context:=gateway_exchange_context native stable discipline resources readonly selected reference owner original.

Theorem actual_exchange_control_pair_before_flags_separate allocation_before allocated environment temporaries data control
    (first:gateway_pair_identity ipc)first_left first_right before world events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  data<>control->selected data->selected control->(forall position,~readonly control position)->
  Mem.range_perm reference control 0 8 Cur Freeable->
  gateway_pair_context native discipline resources ipc first data Ptrofs.zero first_left first_right before world->
  exchange_context before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]
      (exchange_pair_cont exchange_control_stage environment temporaries)before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists pair_events between suffix returned_memory returned_world flags_before flags_world
    (second:gateway_pair_identity ipc)second_left second_right,
    events=pair_events++between++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]Kstop before)world)pair_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop returned_memory)returned_world) /\
    gateway_pair_birth_in_run backend resources ipc control before world pair_events returned_memory returned_world second /\
    pair_right_object ipc first<>pair_right_object ipc second /\
    (4<=second_left)%Z /\(4<=second_right)%Z /\Forall gateway_quiet_event between /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(exchange_pair_cont exchange_control_stage environment temporaries)returned_memory)
        returned_world)between
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
        (PTree.set _t'7(Vint Int.zero)temporaries)flags_before)flags_world) /\
    gateway_pair_context native discipline resources ipc first data Ptrofs.zero first_left first_right flags_before flags_world /\
    gateway_pair_context native discipline resources ipc second control Ptrofs.zero second_left second_right flags_before flags_world /\
    exchange_context flags_before flags_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
        (PTree.set _t'7(Vint Int.zero)temporaries)flags_before)flags_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC SEPARATE DATA_SELECTED CONTROL_SELECTED DISJOINT PERMISSIONS FIRST INITIAL RUN.
  destruct(actual_exchange_pair_returns_zero_before_spawn backend exchange_control_stage environment temporaries control
    allocation_before allocated before world events arguments continuation after next ALLOC RUN)
    as(pair_events&caller_events&returned_memory&returned_world&EVENTS&PAIR&CALLER).
  destruct(actual_exchange_second_pair_preserves_first_separate backend io native stable discipline thread_errno resources ipc thread descriptors
    readonly selected reference owner original first first_left first_right data control before world pair_events returned_memory
    returned_world SEPARATE DATA_SELECTED CONTROL_SELECTED DISJOINT PERMISSIONS FIRST INITIAL PAIR)
    as(second&second_left&second_right&LEFT&RIGHT&BIRTH&OBJECTS&SECOND_CONTEXT&FIRST_CONTEXT&EXCHANGE).
  set(property:=fun memory current=>
    gateway_pair_context native discipline resources ipc first data Ptrofs.zero first_left first_right memory current /\
    gateway_pair_context native discipline resources ipc second control Ptrofs.zero second_left second_right memory current /\
    exchange_context memory current).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current changed later[DATA[CONTROL CONTEXT]]INTERFERENCE;split.
    - eapply gateway_pair_context_ambient;[exact thread|exact descriptors|exact DATA|exact INTERFERENCE].
    - split.
      + eapply gateway_pair_context_ambient;[exact thread|exact descriptors|exact CONTROL|exact INTERFERENCE].
      + eapply gateway_exchange_context_ambient;[exact thread|exact descriptors|exact CONTEXT|exact INTERFERENCE]. }
  set(target:=fun(source:Clight.state)(current:World)=>exists memory,
    source=State f_host_exchange(exchange_setup_after 4)Kstop environment(PTree.set _t'7(Vint Int.zero)temporaries)memory /\
    property memory current).
  assert(SCRIPT:gateway_quiet_launch_path backend target property
    (Returnstate(Vint Int.zero)(exchange_pair_cont exchange_control_stage environment temporaries)returned_memory)).
  { eapply actual_exchange_pair_return_script;[exact CLOSED|exact ALLOC|right;left;reflexivity|].
    intros ZERO;apply gateway_quiet_launch_reached;intros available current READY;exists available;split;[reflexivity|exact READY]. }
  destruct(gateway_quiet_launch_cut backend target property
    (Returnstate(Vint Int.zero)(exchange_pair_cont exchange_control_stage environment temporaries)returned_memory)
    returned_memory returned_world caller_events arguments continuation after next SCRIPT
    (conj FIRST_CONTEXT(conj SECOND_CONTEXT EXCHANGE))CALLER)
    as(between&suffix&flags_source&flags_world&CALLER_EVENTS&QUIET&BETWEEN&POINT&SUFFIX).
  destruct POINT as[flags_before[SOURCE[FIRST_AFTER[SECOND_AFTER CONTEXT_AFTER]]]];subst flags_source.
  exists pair_events,between,suffix,returned_memory,returned_world,flags_before,flags_world,second,second_left,second_right.
  split;[rewrite EVENTS,CALLER_EVENTS;reflexivity|]. split;[exact PAIR|]. split;[exact BIRTH|]. split;[exact OBJECTS|].
  split;[exact LEFT|]. split;[exact RIGHT|]. split;[exact QUIET|]. split;[exact BETWEEN|].
  split;[exact FIRST_AFTER|]. split;[exact SECOND_AFTER|]. split;assumption.
Qed.
Theorem actual_exchange_control_pair_before_flags allocation_before allocated environment temporaries data control
    (first:gateway_pair_identity ipc)first_left first_right before world events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  data<>control->selected data->selected control->(forall position,~readonly control position)->
  Mem.range_perm reference control 0 8 Cur Freeable->
  gateway_pair_context native discipline resources ipc first data Ptrofs.zero first_left first_right before world->
  exchange_context before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]
      (exchange_pair_cont exchange_control_stage environment temporaries)before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists pair_events between suffix returned_memory returned_world flags_before flags_world
    (second:gateway_pair_identity ipc)second_left second_right,
    events=pair_events++between++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]Kstop before)world)pair_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop returned_memory)returned_world) /\
    gateway_pair_birth_in_run backend resources ipc control before world pair_events returned_memory returned_world second /\
    (4<=second_left)%Z /\(4<=second_right)%Z /\Forall gateway_quiet_event between /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(exchange_pair_cont exchange_control_stage environment temporaries)returned_memory)
        returned_world)between
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
        (PTree.set _t'7(Vint Int.zero)temporaries)flags_before)flags_world) /\
    gateway_pair_context native discipline resources ipc first data Ptrofs.zero first_left first_right flags_before flags_world /\
    gateway_pair_context native discipline resources ipc second control Ptrofs.zero second_left second_right flags_before flags_world /\
    exchange_context flags_before flags_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
        (PTree.set _t'7(Vint Int.zero)temporaries)flags_before)flags_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC SEPARATE DATA_SELECTED CONTROL_SELECTED DISJOINT PERMISSIONS FIRST INITIAL RUN.
  destruct(actual_exchange_control_pair_before_flags_separate allocation_before allocated environment temporaries data control first
    first_left first_right before world events arguments continuation after next ALLOC SEPARATE DATA_SELECTED CONTROL_SELECTED DISJOINT
    PERMISSIONS FIRST INITIAL RUN)
    as(pair_events&between&suffix&returned_memory&returned_world&flags_before&flags_world&second&second_left&second_right&
      EVENTS&PAIR&BIRTH&OBJECTS&LEFT&RIGHT&QUIET&BETWEEN&FIRST_AFTER&SECOND_AFTER&CONTEXT&SUFFIX).
  exists pair_events,between,suffix,returned_memory,returned_world,flags_before,flags_world,second,second_left,second_right.
  split;[exact EVENTS|]. split;[exact PAIR|]. split;[exact BIRTH|]. split;[exact LEFT|]. split;[exact RIGHT|].
  split;[exact QUIET|]. split;[exact BETWEEN|]. split;[exact FIRST_AFTER|]. split;[exact SECOND_AFTER|]. split;assumption.
Qed.

End SecondPair.
