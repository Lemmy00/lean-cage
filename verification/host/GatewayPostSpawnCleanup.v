(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One post-spawn source prefix destroys both builders and closes both peers. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayPostSpawnContext GatewayPostSpawnRelease GatewayPostSpawnClose
  GatewayPostSpawnSource GatewayPostSpawnPeers GatewayPostSpawnReleaseSource GatewayPostSpawnPeerSource GatewayTransferMath GatewaySendRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition postspawn_initial_builders actions attributes plan settings:gateway_spawn_builders:=
  {|gateway_builder_actions:=Some(Vptr actions Ptrofs.zero,plan);gateway_builder_attributes:=Some(Vptr attributes Ptrofs.zero,settings)|}.
Definition postspawn_empty_builders:gateway_spawn_builders:=
  {|gateway_builder_actions:=None;gateway_builder_attributes:=None|}.
Definition postspawn_cleanup_temps data_right control_right temporaries:=
  postspawn_peer_temps gateway_parent_control_peer control_right(postspawn_peer_temps gateway_parent_data_peer data_right temporaries).
Definition postspawn_cleanup_leases data_right control_right leases:=gateway_leases_without control_right(gateway_leases_without data_right leases).

Section Cleanup.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources ipc builders genuine footprint
  (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
  (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:Values.block->Z->Prop)(selected:Values.block->Prop)(reference:mem)(owner:World)
  (data control:Values.block)(data_left data_right control_left control_right:Z)(actions attributes:Values.block).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(ACTIONS_SELECTED:selected actions)(ATTRIBUTES_SELECTED:selected attributes)
  (ACTIONS_DATA:actions<>data)(ACTIONS_CONTROL:actions<>control)(ATTRIBUTES_DATA:attributes<>data)(ATTRIBUTES_CONTROL:attributes<>control)
  (ACTIONS_READONLY:forall position,~readonly actions position)(ATTRIBUTES_READONLY:forall position,~readonly attributes position)
  (ACTIONS_RANGE:Mem.range_perm reference actions 0 80 Cur Freeable)(ATTRIBUTES_RANGE:Mem.range_perm reference attributes 0 336 Cur Freeable).
Local Definition context:=gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
  data control data_left data_right control_left control_right.

Theorem actual_postspawn_cleanup plan settings leases data_entry control_entry allocation_before allocated environment temporaries
    before world events value after next descriptor:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_actions=Some(actions,gateway_actions_type)->environment!_attributes=Some(attributes,gateway_attributes_type)->
  environment!_pair=Some(data,tarray tint 2)->environment!_control=Some(control,tarray tint 2)->
  context(postspawn_initial_builders actions attributes plan settings)leases before world->
  In(data_right,data_entry)leases->In(control_right,control_entry)leases->data_right<>control_right->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(postspawn_after 0)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(postspawn_after 0)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(postspawn_after 4)Kstop environment
        (postspawn_cleanup_temps data_right control_right temporaries)memory)current) /\
    context postspawn_empty_builders(postspawn_cleanup_leases data_right control_right leases)memory current /\
    gateway_received_bytes io descriptor prefix=[] /\gateway_sent_bytes io descriptor prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(postspawn_after 4)Kstop environment
        (postspawn_cleanup_temps data_right control_right temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC ACTIONS ATTRIBUTES DATA CONTROL READY DATA_ENTRY CONTROL_ENTRY SEPARATE RUN.
  set(initial:=postspawn_initial_builders actions attributes plan settings).
  set(first:=gateway_release_done gateway_release_attributes initial).
  destruct(actual_postspawn_destroy_source backend io native stable discipline thread_errno resources ipc builders genuine footprint
    runtime descriptors sdk readonly selected reference owner data control data_left data_right control_left control_right
    DATA_SELECTED CONTROL_SELECTED gateway_release_attributes initial leases attributes allocation_before allocated environment temporaries
    before world events value after next descriptor ALLOC ATTRIBUTES READY ATTRIBUTES_SELECTED ATTRIBUTES_DATA ATTRIBUTES_CONTROL
    ATTRIBUTES_READONLY ATTRIBUTES_RANGE ltac:(exists settings;reflexivity)RUN)
    as(p1 & r1 & m1 & w1 & E1 & P1 & R1 & I1 & O1 & S1).
  destruct(actual_postspawn_destroy_source backend io native stable discipline thread_errno resources ipc builders genuine footprint
    runtime descriptors sdk readonly selected reference owner data control data_left data_right control_left control_right
    DATA_SELECTED CONTROL_SELECTED gateway_release_actions first leases actions allocation_before allocated environment temporaries
    m1 w1 r1 value after next descriptor ALLOC ACTIONS R1 ACTIONS_SELECTED ACTIONS_DATA ACTIONS_CONTROL
    ACTIONS_READONLY ACTIONS_RANGE ltac:(exists plan;reflexivity)S1)
    as(p2 & r2 & m2 & w2 & E2 & P2 & R2 & I2 & O2 & S2).
  change(context postspawn_empty_builders leases m2 w2)in R2.
  destruct(actual_postspawn_peer_source backend io native stable discipline thread_errno resources ipc builders genuine footprint
    runtime descriptors sdk readonly selected reference owner data control data_left data_right control_left control_right
    DATA_SELECTED CONTROL_SELECTED gateway_parent_data_peer postspawn_empty_builders leases data_entry allocation_before allocated
    environment temporaries m2 w2 r2 value after next descriptor ALLOC DATA R2 DATA_ENTRY S2)
    as(p3 & r3 & m3 & w3 & E3 & P3 & R3 & I3 & O3 & S3).
  assert(CONTROL_KEPT:In(control_right,control_entry)(gateway_leases_without data_right leases)).
  { unfold gateway_leases_without;apply filter_In;split;[exact CONTROL_ENTRY|].
    apply negb_true_iff,Z.eqb_neq;cbn;congruence. }
  destruct(actual_postspawn_peer_source backend io native stable discipline thread_errno resources ipc builders genuine footprint
    runtime descriptors sdk readonly selected reference owner data control data_left data_right control_left control_right
    DATA_SELECTED CONTROL_SELECTED gateway_parent_control_peer postspawn_empty_builders(gateway_leases_without data_right leases)
    control_entry allocation_before allocated environment(postspawn_peer_temps gateway_parent_data_peer data_right temporaries)
    m3 w3 r3 value after next descriptor ALLOC CONTROL R3 CONTROL_KEPT S3)
    as(p4 & suffix & memory & current & E4 & P4 & FINAL & I4 & O4 & SUFFIX).
  exists(p1++p2++p3++p4),suffix,memory,current.
  split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;reflexivity|].
  split.
  - eapply gateway_steps_append;[exact P1|]. eapply gateway_steps_append;[exact P2|].
    eapply gateway_steps_append;[exact P3|exact P4].
  - split;[exact FINAL|]. split.
    + rewrite !gateway_received_bytes_append,I1,I2,I3,I4;reflexivity.
    + split;[rewrite !gateway_sent_bytes_append,O1,O2,O3,O4;reflexivity|exact SUFFIX].
Qed.
End Cleanup.
