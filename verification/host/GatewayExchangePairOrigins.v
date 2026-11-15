(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The exact first and second pair copyouts
   occur in the prefix before SDK setup of the original exchange. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFramedRuntime GatewayReadonly
  GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewayPassiveResources
  GatewayPairContext GatewayPairHistory GatewayPairSource GatewayPairOccurrence GatewayPairPosition GatewayPairReference
  GatewayPairKernelOrigin GatewayExchangeContext GatewayExchangeSetup GatewayExchangeClockPaths GatewayExchangeClock
  GatewayExchangePairPaths GatewayExchangePairReturns GatewayExchangePairContext GatewayExchangePairCall GatewayLaunchQuiet
  GatewayExchangeConnections GatewayExchangeFirstPair GatewayExchangeSecondContext GatewayExchangeSecondPair GatewaySpawnTopology GatewayCallerRetention GatewayCallerFamily GatewayCallerBuffers GatewayCallerClockResources GatewayBufferReference.
From HostGateway Require Import GatewayPairCopyout.
Import ListNotations.
Module PairOriginFirst.
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
    gateway_copyout_pair_birth backend resources ipc data before world pair_events returned_memory returned_world identity /\
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
  destruct(actual_exchange_pair_copyout backend io native stable discipline thread_errno resources ipc thread descriptors
    readonly selected reference owner original data before world pair_events returned_memory returned_world
    DISJOINT SELECTED PERMISSIONS INITIAL PAIR)as(identity&left&right&LEFT&RIGHT&BIRTH&ORIGIN&PAIR_CONTEXT&EXCHANGE).
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
End PairOriginFirst.

Module PairOriginRetention.
Section SecondContext.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state).

Theorem actual_exchange_second_pair_preserves_first_separate(identity:gateway_pair_identity ipc)left right data control
    before world events after next:
  data<>control->selected data->selected control->(forall position,~readonly control position)->
  Mem.range_perm reference control 0 8 Cur Freeable->
  gateway_pair_context native discipline resources ipc identity data Ptrofs.zero left right before world->
  gateway_exchange_context native stable discipline resources readonly selected reference owner original before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists(second:gateway_pair_identity ipc)second_left second_right,
    (4<=second_left)%Z /\(4<=second_right)%Z /\
    gateway_copyout_pair_birth backend resources ipc control before world events after next second /\
    pair_right_object ipc identity<>pair_right_object ipc second /\
    gateway_pair_context native discipline resources ipc second control Ptrofs.zero second_left second_right after next /\
    gateway_pair_context native discipline resources ipc identity data Ptrofs.zero left right after next /\
    gateway_exchange_context native stable discipline resources readonly selected reference owner original after next.
Proof.
  intros SEPARATE DATA_SELECTED CONTROL_SELECTED READONLY_SEPARATE PERMISSIONS FIRST INITIAL RUN.
  destruct INITIAL as[SIDE[[VALID ORIGINAL]FAMILY]].
  set(expanded:=fun object position=>readonly object position \/object=data).
  assert(NEW_FAMILY:gateway_caller_family native stable expanded selected before world before world).
  { apply gateway_caller_family_refl.
    - intros object SELECTED;destruct(FAMILY object SELECTED)as[LIVE[PRIVATE REST]];split;assumption.
    - intros object position[HERE|SAME].
      + exact((proj1(proj2(proj2(FAMILY control CONTROL_SELECTED))))object position HERE).
      + subst object;split;[exact(proj1(FAMILY data DATA_SELECTED))|].
        left;exact(proj1(proj2(FAMILY data DATA_SELECTED))). }
  assert(CONTROL_RANGE:Mem.range_perm before control 0 8 Cur Freeable).
  { eapply gateway_caller_family_current_range;[exact FAMILY|exact CONTROL_SELECTED|exact PERMISSIONS]. }
  assert(NEW_INITIAL:gateway_exchange_context native stable discipline resources expanded selected before world
    (resources world)before world).
  { split;[exact SIDE|]. split;[split;[exact VALID|apply gateway_resource_reference_refl]|exact NEW_FAMILY]. }
  destruct(actual_exchange_pair_copyout backend io native stable discipline thread_errno resources ipc thread descriptors
    expanded selected before world(resources world)control before world events after next
    ltac:(intros position[HERE|SAME];[exact(READONLY_SEPARATE position HERE)|congruence])
    CONTROL_SELECTED CONTROL_RANGE NEW_INITIAL RUN)
    as(second&second_left&second_right&LEFT&RIGHT&BIRTH&ORIGIN&SECOND&AFTER).
  destruct AFTER as[NORMAL[[AFTER_VALID REFERENCE]AFTER_FAMILY]].
  destruct FIRST as[FIRST_SIDE[FIRST_PRIVATE[FIRST_CELLS FIRST_RESOURCES]]].
  assert(RETAINED_FIRST:gateway_pair_context native discipline resources ipc identity data Ptrofs.zero left right after next).
  { split;[exact NORMAL|]. split;[exact(proj1(proj2(AFTER_FAMILY data DATA_SELECTED)))|]. split.
    - eapply gateway_pair_cells_unchanged;[exact FIRST_CELLS|].
      destruct(AFTER_FAMILY control CONTROL_SELECTED)as[LIVE[PRIVATE[READONLY[[FRAME CURRENT]REST]]]].
      eapply Mem.unchanged_on_implies;[exact FRAME|].
      intros object position[SAME RANGE]LIVE_BEFORE;right;exact SAME.
    - eapply gateway_pair_resources_reference;[exact FIRST_RESOURCES|exact AFTER_VALID|exact REFERENCE]. }
  assert(SEPARATE_RIGHT:pair_right_object ipc identity<>pair_right_object ipc second).
  { pose proof(proj1(proj2(proj2(proj2(proj2(proj2 FIRST_RESOURCES))))))as FIRST_RIGHT.
    pose proof(gateway_resource_reference_owned _ _ _ _ ORIGIN FIRST_RIGHT)as OLD_RIGHT.
    pose proof(gateway_owned_object_born _ _ _(gateway_pair_original_valid ipc second second_left second_right
      (resources next)(proj2(proj2(proj2 SECOND))))OLD_RIGHT)as BORN_RIGHT.
    change(gateway_resource_objects(pair_origin ipc second)(pair_right_object ipc identity)=true)in BORN_RIGHT.
    intro SAME;rewrite SAME,(pair_right_fresh ipc second)in BORN_RIGHT;discriminate. }
  exists second,second_left,second_right.
  split;[exact LEFT|]. split;[exact RIGHT|]. split;[exact BIRTH|]. split;[exact SEPARATE_RIGHT|]. split;[exact SECOND|].
  split;[exact RETAINED_FIRST|]. split;[exact NORMAL|]. split.
  - split;[exact AFTER_VALID|]. eapply gateway_resource_reference_transitive;[exact ORIGINAL|exact REFERENCE].
  - eapply gateway_caller_family_rebase;[exact FAMILY|exact AFTER_FAMILY|]. intros;left;assumption.
Qed.
End SecondContext.
End PairOriginRetention.

Module PairOriginControl.
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
    gateway_copyout_pair_birth backend resources ipc control before world pair_events returned_memory returned_world second /\
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
  destruct(PairOriginRetention.actual_exchange_second_pair_preserves_first_separate backend io native stable discipline thread_errno resources ipc thread descriptors
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
End SecondPair.
End PairOriginControl.

Module PairOriginConnections.
Section Connections.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (passive:gateway_passive_resource_runtime backend resources).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state).
Local Definition context:=gateway_exchange_context native stable discipline resources readonly selected reference owner original.

Theorem actual_exchange_connections_before_flags_distinct allocation_before allocated environment temporaries data control
    before world events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_pair=Some(data,tarray tint 2)->environment!_control=Some(control,tarray tint 2)->data<>control->
  selected data->selected control->(forall position,~readonly data position)->(forall position,~readonly control position)->
  Mem.range_perm reference data 0 8 Cur Freeable->Mem.range_perm reference control 0 8 Cur Freeable->context before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists began prefix suffix flags_before flags_world(data_identity control_identity:gateway_pair_identity ipc)
    data_left data_right control_left control_right,
    events=prefix++suffix /\exchange_clock_truth began=Some true /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
        (exchange_connections_temps began temporaries)flags_before)flags_world) /\
    pair_right_object ipc data_identity<>pair_right_object ipc control_identity /\
    (4<=data_left)%Z /\(4<=data_right)%Z /\(4<=control_left)%Z /\(4<=control_right)%Z /\
    gateway_pair_context native discipline resources ipc data_identity data Ptrofs.zero data_left data_right flags_before flags_world /\
    gateway_pair_context native discipline resources ipc control_identity control Ptrofs.zero control_left control_right flags_before flags_world /\
    context flags_before flags_world /\
    gateway_copyout_pairs_slice_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world prefix
      (State f_host_exchange(exchange_setup_after 4)Kstop environment
        (exchange_connections_temps began temporaries)flags_before)flags_world data_identity control_identity /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
        (exchange_connections_temps began temporaries)flags_before)flags_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_DISJOINT CONTROL_DISJOINT DATA_RANGE CONTROL_RANGE INITIAL RUN.
  destruct(actual_exchange_clock_before_data_pair backend io native stable discipline thread_errno resources ipc thread descriptors passive
    readonly selected reference owner original allocation_before allocated environment temporaries data before world events arguments
    continuation after next Int.zero ALLOC DATA ltac:(exists data;exact DATA_SELECTED)INITIAL RUN)
    as(clock_prefix&clock_events&clock_guard&after_clock&clock_before&clock_world&began&clock_after&returned_world&data_before&data_world&
      EVENTS&QUIET_CLOCK&QUIET_GUARD&CLOCK_PREFIX&CLOCK_INITIAL&CLOCK&CLOCK_GUARD&NONZERO&DATA_INITIAL&EMPTY_CLOCK&AFTER_CLOCK).
  destruct(PairOriginFirst.actual_exchange_data_pair_before_control backend io native stable discipline thread_errno resources ipc thread descriptors
    readonly selected reference owner original allocation_before allocated environment(exchange_clock_temps began temporaries)data control
    data_before data_world after_clock arguments continuation after next ALLOC CONTROL DATA_DISJOINT DATA_SELECTED DATA_RANGE DATA_INITIAL
    AFTER_CLOCK)
    as(data_events&data_guard&after_data&data_after&data_returned_world&control_before&control_world&data_identity&data_left&data_right&
      AFTER_CLOCK_EVENTS&DATA_RUN&DATA_BIRTH&DATA_LEFT&DATA_RIGHT&QUIET_DATA_GUARD&DATA_GUARD&DATA_AT_CONTROL&CONTROL_INITIAL&AFTER_DATA).
  destruct(PairOriginControl.actual_exchange_control_pair_before_flags_separate backend io native stable discipline thread_errno resources ipc thread descriptors
    readonly selected reference owner original allocation_before allocated environment
    (PTree.set _t'3(Vint Int.zero)(exchange_clock_temps began temporaries))data control data_identity data_left data_right
    control_before control_world after_data arguments continuation after next ALLOC SEPARATE DATA_SELECTED CONTROL_SELECTED
    CONTROL_DISJOINT CONTROL_RANGE DATA_AT_CONTROL CONTROL_INITIAL AFTER_DATA)
    as(control_events&control_guard&suffix&control_after&control_returned_world&flags_before&flags_world&control_identity&control_left&control_right&
      AFTER_DATA_EVENTS&CONTROL_RUN&CONTROL_BIRTH&OBJECTS&CONTROL_LEFT&CONTROL_RIGHT&QUIET_CONTROL_GUARD&CONTROL_GUARD&DATA_AT_FLAGS&CONTROL_AT_FLAGS&
      FLAGS_CONTEXT&SUFFIX).
  set(source:=State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before).
  set(to_data:=clock_prefix++clock_events++clock_guard).
  assert(DATA_PREFIX:gateway_steps backend(Clight.globalenv prog)(gateway_live source world)to_data
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr data Ptrofs.zero]
      (exchange_pair_cont exchange_data_stage environment(exchange_clock_temps began temporaries))data_before)data_world)).
  { eapply gateway_steps_append;[exact CLOCK_PREFIX|].
    eapply gateway_steps_append;[|exact CLOCK_GUARD].
    exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(exchange_clock_cont environment temporaries)I CLOCK). }
  set(to_control:=to_data++data_events++data_guard).
  assert(CONTROL_PREFIX:gateway_steps backend(Clight.globalenv prog)(gateway_live source world)to_control
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]
      (exchange_pair_cont exchange_control_stage environment(PTree.set _t'3(Vint Int.zero)(exchange_clock_temps began temporaries)))
      control_before)control_world)).
  { eapply gateway_steps_append;[exact DATA_PREFIX|].
    eapply gateway_steps_append;[|exact DATA_GUARD].
    exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _
      (exchange_pair_cont exchange_data_stage environment(exchange_clock_temps began temporaries))I DATA_RUN). }
  set(prefix:=to_control++control_events++control_guard).
  assert(FLAGS_PREFIX:gateway_steps backend(Clight.globalenv prog)(gateway_live source world)prefix
    (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
      (exchange_connections_temps began temporaries)flags_before)flags_world)).
  { eapply gateway_steps_append;[exact CONTROL_PREFIX|].
    eapply gateway_steps_append;[|exact CONTROL_GUARD].
    exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _
      (exchange_pair_cont exchange_control_stage environment(PTree.set _t'3(Vint Int.zero)(exchange_clock_temps began temporaries)))
      I CONTROL_RUN). }
  set(target:=State f_host_exchange(exchange_setup_after 4)Kstop environment
    (exchange_connections_temps began temporaries)flags_before).
  assert(DATA_TAIL:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)
      (exchange_pair_cont exchange_data_stage environment(exchange_clock_temps began temporaries))data_after)data_returned_world)
    (data_guard++control_events++control_guard)(gateway_live target flags_world)).
  { eapply gateway_steps_append;[exact DATA_GUARD|].
    eapply gateway_steps_append;[|exact CONTROL_GUARD].
    exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _
      (exchange_pair_cont exchange_control_stage environment(PTree.set _t'3(Vint Int.zero)(exchange_clock_temps began temporaries)))
      I CONTROL_RUN). }
  assert(DATA_EVENTS:prefix=to_data++data_events++(data_guard++control_events++control_guard)).
  { unfold prefix,to_control;repeat rewrite <-app_assoc;reflexivity. }
  assert(CONTROL_EVENTS:prefix=to_control++control_events++control_guard)by reflexivity.
  destruct(gateway_copyout_pair_slice_positioned backend resources ipc data source world to_data data_events(data_guard++control_events++control_guard)
    (exchange_pair_cont exchange_data_stage environment(exchange_clock_temps began temporaries))data_before data_world data_after
    data_returned_world data_identity prefix target flags_world I DATA_EVENTS DATA_PREFIX DATA_BIRTH DATA_TAIL)as[data_ordinal[DATA_POSITION DATA_AT]].
  destruct(gateway_copyout_pair_slice_positioned backend resources ipc control source world to_control control_events control_guard
    (exchange_pair_cont exchange_control_stage environment(PTree.set _t'3(Vint Int.zero)(exchange_clock_temps began temporaries)))
    control_before control_world control_after control_returned_world control_identity prefix target flags_world I CONTROL_EVENTS CONTROL_PREFIX CONTROL_BIRTH CONTROL_GUARD)
    as[control_ordinal[CONTROL_POSITION CONTROL_AT]].
  assert(ORDER:(data_ordinal<control_ordinal)%nat).
  { unfold to_control in CONTROL_POSITION;repeat rewrite app_length in CONTROL_POSITION;lia. }
  exists began,prefix,suffix,flags_before,flags_world,data_identity,control_identity,data_left,data_right,control_left,control_right.
  split.
  - unfold prefix,to_control,to_data;rewrite EVENTS,AFTER_CLOCK_EVENTS,AFTER_DATA_EVENTS;repeat rewrite <-app_assoc;reflexivity.
  - split;[exact NONZERO|]. split;[exact FLAGS_PREFIX|]. split;[exact OBJECTS|].
    split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|]. split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|].
    split;[exact DATA_AT_FLAGS|]. split;[exact CONTROL_AT_FLAGS|]. split;[exact FLAGS_CONTEXT|]. split.
    + exists data_ordinal,control_ordinal;split;[exact ORDER|]. split;assumption.
    + exact SUFFIX.
Qed.
End Connections.
End PairOriginConnections.
