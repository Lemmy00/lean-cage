(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: One actual exchange reaches setup with its two source-created connections. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayReadonly GatewayThreadRuntime
  GatewayStreamInterface GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewayPassiveResources GatewayPairContext
  GatewayPairOccurrence GatewayPairPosition GatewayExchangeContext GatewayExchangeSetup GatewayExchangeClockPaths GatewayExchangeClock
  GatewayExchangePairPaths GatewayExchangeFirstPair GatewayExchangeSecondPair.
Import ListNotations.

Definition exchange_connections_temps began temporaries:=
  PTree.set _t'7(Vint Int.zero)(PTree.set _t'3(Vint Int.zero)(exchange_clock_temps began temporaries)).

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
    gateway_source_pair_birth backend resources ipc data
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity /\
    gateway_source_pair_birth backend resources ipc control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events control_identity /\
    pair_right_object ipc data_identity<>pair_right_object ipc control_identity /\
    (4<=data_left)%Z /\(4<=data_right)%Z /\(4<=control_left)%Z /\(4<=control_right)%Z /\
    gateway_pair_context native discipline resources ipc data_identity data Ptrofs.zero data_left data_right flags_before flags_world /\
    gateway_pair_context native discipline resources ipc control_identity control Ptrofs.zero control_left control_right flags_before flags_world /\
    context flags_before flags_world /\
    gateway_source_pairs_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity control_identity /\
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
  destruct(actual_exchange_data_pair_before_control backend io native stable discipline thread_errno resources ipc thread descriptors
    readonly selected reference owner original allocation_before allocated environment(exchange_clock_temps began temporaries)data control
    data_before data_world after_clock arguments continuation after next ALLOC CONTROL DATA_DISJOINT DATA_SELECTED DATA_RANGE DATA_INITIAL
    AFTER_CLOCK)
    as(data_events&data_guard&after_data&data_after&data_returned_world&control_before&control_world&data_identity&data_left&data_right&
      AFTER_CLOCK_EVENTS&DATA_RUN&DATA_BIRTH&DATA_LEFT&DATA_RIGHT&QUIET_DATA_GUARD&DATA_GUARD&DATA_AT_CONTROL&CONTROL_INITIAL&AFTER_DATA).
  destruct(actual_exchange_control_pair_before_flags_separate backend io native stable discipline thread_errno resources ipc thread descriptors
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
  assert(DATA_EVENTS:events=to_data++data_events++(data_guard++after_data)).
  { unfold to_data;rewrite EVENTS,AFTER_CLOCK_EVENTS;repeat rewrite <-app_assoc;reflexivity. }
  assert(CONTROL_EVENTS:events=to_control++control_events++(control_guard++suffix)).
  { unfold to_control,to_data;rewrite EVENTS,AFTER_CLOCK_EVENTS,AFTER_DATA_EVENTS;repeat rewrite <-app_assoc;reflexivity. }
  destruct(gateway_pair_positioned_in_caller backend resources ipc data source world to_data data_events(data_guard++after_data)
    (exchange_pair_cont exchange_data_stage environment(exchange_clock_temps began temporaries))data_before data_world data_after
    data_returned_world data_identity events I DATA_EVENTS DATA_PREFIX DATA_BIRTH)as[data_ordinal[DATA_POSITION DATA_AT]].
  destruct(gateway_pair_positioned_in_caller backend resources ipc control source world to_control control_events(control_guard++suffix)
    (exchange_pair_cont exchange_control_stage environment(PTree.set _t'3(Vint Int.zero)(exchange_clock_temps began temporaries)))
    control_before control_world control_after control_returned_world control_identity events I CONTROL_EVENTS CONTROL_PREFIX CONTROL_BIRTH)
    as[control_ordinal[CONTROL_POSITION CONTROL_AT]].
  assert(ORDER:(data_ordinal<control_ordinal)%nat).
  { unfold to_control in CONTROL_POSITION;repeat rewrite app_length in CONTROL_POSITION;lia. }
  exists began,prefix,suffix,flags_before,flags_world,data_identity,control_identity,data_left,data_right,control_left,control_right.
  split.
  - unfold prefix,to_control,to_data;rewrite EVENTS,AFTER_CLOCK_EVENTS,AFTER_DATA_EVENTS;repeat rewrite <-app_assoc;reflexivity.
  - split;[exact NONZERO|]. split;[exact FLAGS_PREFIX|]. split.
    + eapply gateway_pair_birth_in_caller with(prefix:=to_data)(helper_events:=data_events)(suffix:=data_guard++after_data)
        (continuation:=exchange_pair_cont exchange_data_stage environment(exchange_clock_temps began temporaries));
        [exact I| |exact DATA_PREFIX|exact DATA_BIRTH].
      unfold to_data;rewrite EVENTS,AFTER_CLOCK_EVENTS;repeat rewrite <-app_assoc;reflexivity.
    + split.
      * eapply gateway_pair_birth_in_caller with(prefix:=to_control)(helper_events:=control_events)(suffix:=control_guard++suffix)
          (continuation:=exchange_pair_cont exchange_control_stage environment
            (PTree.set _t'3(Vint Int.zero)(exchange_clock_temps began temporaries)));
          [exact I| |exact CONTROL_PREFIX|exact CONTROL_BIRTH].
        unfold to_control,to_data;rewrite EVENTS,AFTER_CLOCK_EVENTS,AFTER_DATA_EVENTS;repeat rewrite <-app_assoc;reflexivity.
      * split;[exact OBJECTS|]. split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|]. split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|].
        split;[exact DATA_AT_FLAGS|]. split;[exact CONTROL_AT_FLAGS|]. split;[exact FLAGS_CONTEXT|]. split.
        -- exists data_ordinal,control_ordinal;split;[exact ORDER|]. split;assumption.
        -- exact SUFFIX.
Qed.
Theorem actual_exchange_connections_before_flags_ordered allocation_before allocated environment temporaries data control
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
    gateway_source_pair_birth backend resources ipc data
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity /\
    gateway_source_pair_birth backend resources ipc control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events control_identity /\
    (4<=data_left)%Z /\(4<=data_right)%Z /\(4<=control_left)%Z /\(4<=control_right)%Z /\
    gateway_pair_context native discipline resources ipc data_identity data Ptrofs.zero data_left data_right flags_before flags_world /\
    gateway_pair_context native discipline resources ipc control_identity control Ptrofs.zero control_left control_right flags_before flags_world /\
    context flags_before flags_world /\
    gateway_source_pairs_ordered backend resources ipc data control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity control_identity /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
        (exchange_connections_temps began temporaries)flags_before)flags_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_DISJOINT CONTROL_DISJOINT DATA_RANGE CONTROL_RANGE INITIAL RUN.
  destruct(actual_exchange_connections_before_flags_distinct allocation_before allocated environment temporaries data control
    before world events arguments continuation after next ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_DISJOINT
    CONTROL_DISJOINT DATA_RANGE CONTROL_RANGE INITIAL RUN)
    as(began&prefix&suffix&flags_before&flags_world&data_identity&control_identity&data_left&data_right&control_left&control_right&
      EVENTS&NONZERO&PREFIX&DATA_BIRTH&CONTROL_BIRTH&OBJECTS&DATA_LEFT&DATA_RIGHT&CONTROL_LEFT&CONTROL_RIGHT&DATA_CONTEXT&CONTROL_CONTEXT&
      CONTEXT&ORDER&SUFFIX).
  exists began,prefix,suffix,flags_before,flags_world,data_identity,control_identity,data_left,data_right,control_left,control_right.
  split;[exact EVENTS|]. split;[exact NONZERO|]. split;[exact PREFIX|]. split;[exact DATA_BIRTH|]. split;[exact CONTROL_BIRTH|].
  split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|]. split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|].
  split;[exact DATA_CONTEXT|]. split;[exact CONTROL_CONTEXT|]. split;[exact CONTEXT|]. split;assumption.
Qed.

Theorem actual_exchange_connections_before_flags allocation_before allocated environment temporaries data control
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
    gateway_source_pair_birth backend resources ipc data
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events data_identity /\
    gateway_source_pair_birth backend resources ipc control
      (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world events control_identity /\
    (4<=data_left)%Z /\(4<=data_right)%Z /\(4<=control_left)%Z /\(4<=control_right)%Z /\
    gateway_pair_context native discipline resources ipc data_identity data Ptrofs.zero data_left data_right flags_before flags_world /\
    gateway_pair_context native discipline resources ipc control_identity control Ptrofs.zero control_left control_right flags_before flags_world /\
    context flags_before flags_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 4)Kstop environment
        (exchange_connections_temps began temporaries)flags_before)flags_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_DISJOINT CONTROL_DISJOINT DATA_RANGE CONTROL_RANGE INITIAL RUN.
  destruct(actual_exchange_connections_before_flags_ordered allocation_before allocated environment temporaries data control
    before world events arguments continuation after next ALLOC DATA CONTROL SEPARATE DATA_SELECTED CONTROL_SELECTED DATA_DISJOINT
    CONTROL_DISJOINT DATA_RANGE CONTROL_RANGE INITIAL RUN)
    as(began&prefix&suffix&flags_before&flags_world&data_identity&control_identity&data_left&data_right&control_left&control_right&
      EVENTS&NONZERO&PREFIX&DATA_BIRTH&CONTROL_BIRTH&DATA_LEFT&DATA_RIGHT&CONTROL_LEFT&CONTROL_RIGHT&DATA_CONTEXT&CONTROL_CONTEXT&
      CONTEXT&ORDER&SUFFIX).
  exists began,prefix,suffix,flags_before,flags_world,data_identity,control_identity,data_left,data_right,control_left,control_right.
  split;[exact EVENTS|]. split;[exact NONZERO|]. split;[exact PREFIX|]. split;[exact DATA_BIRTH|]. split;[exact CONTROL_BIRTH|].
  split;[exact DATA_LEFT|]. split;[exact DATA_RIGHT|]. split;[exact CONTROL_LEFT|]. split;[exact CONTROL_RIGHT|].
  split;[exact DATA_CONTEXT|]. split;[exact CONTROL_CONTEXT|]. split;assumption.
Qed.
End Connections.
