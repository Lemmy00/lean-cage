(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real post-spawn caller closes only its selected parent peer leases. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayOperations GatewayRuntimeCuts GatewayReadonly
  GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions
  GatewayPostSpawnContext GatewayPostSpawnClose GatewayPostSpawnCalls GatewayPostSpawnSource GatewayPostSpawnPeers GatewayPairContext GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayPrimitiveCalls GatewayTransferMath GatewaySendRuntime.
Import ListNotations.
Open Scope Z_scope.

Section Source.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources ipc builders genuine footprint
  (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
  (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:Values.block->Z->Prop)(selected:Values.block->Prop)(reference:mem)(owner:World)
  (data control:Values.block)(data_left data_right control_left control_right:Z).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control).
Local Definition context:=gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
  data control data_left data_right control_left control_right.
Local Lemma context_closed expected leases:gateway_ambient_closed backend(context expected leases).
Proof. eapply gateway_postspawn_ambient;[exact runtime|exact descriptors|exact sdk|exact DATA_SELECTED|exact CONTROL_SELECTED]. Qed.

Definition source_peer_object peer:=match peer with gateway_parent_data_peer=>data|gateway_parent_control_peer=>control end.
Definition source_peer_left peer:=match peer with gateway_parent_data_peer=>data_left|gateway_parent_control_peer=>control_left end.
Definition source_peer_right peer:=match peer with gateway_parent_data_peer=>data_right|gateway_parent_control_peer=>control_right end.

Theorem actual_postspawn_peer_source peer expected leases entry allocation_before allocated environment temporaries
    before world events value after next descriptor:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!(postspawn_peer_identifier peer)=Some(source_peer_object peer,Ctypesdefs.tarray Ctypesdefs.tint 2)->
  context expected leases before world->In(source_peer_right peer,entry)leases->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(postspawn_after(postspawn_peer_index peer))Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(postspawn_after(postspawn_peer_index peer))Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(postspawn_after(S(postspawn_peer_index peer)))Kstop environment
        (postspawn_peer_temps peer(source_peer_right peer)temporaries)memory)current) /\
    context expected(gateway_leases_without(source_peer_right peer)leases)memory current /\
    gateway_received_bytes io descriptor prefix=[] /\gateway_sent_bytes io descriptor prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(postspawn_after(S(postspawn_peer_index peer)))Kstop environment
        (postspawn_peer_temps peer(source_peer_right peer)temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC ARRAY READY MEMBER RUN.
  set(loaded:=postspawn_peer_temps peer(source_peer_right peer)temporaries).
  assert(CELLS:forall memory current,context expected leases memory current->
    GatewayPairContext.gateway_pair_cells memory(source_peer_object peer)Ptrofs.zero(source_peer_left peer)(source_peer_right peer)).
  { intros memory current GOOD;destruct GOOD as[SIDE VALID GENUINE BUILDERS FAMILY DATA CONTROL LEASES];destruct peer;assumption. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events(Returnstate value Kstop after)next
    (actual_postspawn_peer_prefix backend(context expected leases)(context_closed expected leases)peer
      allocation_before allocated environment temporaries before(source_peer_object peer)(source_peer_left peer)(source_peer_right peer)
      ALLOC ARRAY CELLS)I READY RUN)
    as(p1 & r1 & m1 & w1 & E1 & Q1 & P1 & R1 & S1).
  cbn[gateway_replace_memory]in P1,S1.
  destruct(gateway_return_cut backend(Clight.globalenv prog)(gateway_spawn_signature gateway_close_api)[Vint(Int.repr(source_peer_right peer))]
    (postspawn_peer_cont peer environment loaded)m1 w1 r1(Returnstate value Kstop after)next I ltac:(cbn;lia)S1)
    as(p2 & r2 & returned & m2 & w2 & E2 & BODY & S2).
  destruct(actual_postspawn_close backend io native stable discipline thread_errno resources ipc builders genuine footprint runtime
    descriptors sdk readonly selected reference owner data control data_left data_right control_left control_right DATA_SELECTED CONTROL_SELECTED
    (Clight.globalenv prog)expected leases(source_peer_right peer)entry m1 w1 p2 returned m2 w2 descriptor
    R1 MEMBER BODY)as[RESULT[R2[INPUT_EMPTY OUTPUT_EMPTY]]].
  set(kept:=gateway_leases_without(source_peer_right peer)leases).
  destruct(gateway_uniform_edge_side_cut backend(Clight.globalenv prog)(context expected kept)(context_closed expected kept)
    (Returnstate returned(postspawn_peer_cont peer environment loaded)m2)
    (State f_host_exchange Sskip(Kseq(postspawn_after(S(postspawn_peer_index peer)))Kstop)environment loaded m2)
    m2 w2 r2 value after next ltac:(cbn;tauto)ltac:(intros;apply unchanged_store_edge,edge_returnstate)R2 S2)
    as(p3 & r3 & m3 & w3 & E3 & Q3 & P3 & R3 & S3).
  cbn[gateway_replace_memory]in P3,S3.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m3 w3 r3(Returnstate value Kstop after)next
    (actual_postspawn_return_next backend(Clight.globalenv prog)(context expected kept)(context_closed expected kept)
      (postspawn_peer_index peer)environment loaded m3)I R3 S3)
    as(p4 & suffix & memory & current & E4 & Q4 & P4 & FINAL & SUFFIX).
  cbn[gateway_replace_memory]in P4,SUFFIX.
  assert(PENDING:Forall gateway_pending_event p3).
  { eapply Forall_impl;[|exact Q3];intros event SAME;left;exact SAME. }
  exists(p1++p2++p3++gateway_source E0::p4),suffix,memory,current.
  split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;reflexivity|].
  split.
  - eapply gateway_steps_append;[exact P1|].
    eapply gateway_steps_append;[exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _
      (postspawn_peer_cont peer environment loaded)I BODY)|].
    eapply gateway_steps_append;[exact P3|].
    econstructor;[apply gateway_internal;[cbn;tauto|constructor;reflexivity]|exact P4].
  - split;[exact FINAL|]. split.
    + rewrite !gateway_received_bytes_append,(gateway_quiet_received_empty io descriptor p1 Q1),INPUT_EMPTY,
        (gateway_pending_received_empty io descriptor p3 PENDING).
      change(gateway_received_bytes io descriptor p4=[]);apply gateway_quiet_received_empty;exact Q4.
    + split.
      * rewrite !gateway_sent_bytes_append,(gateway_quiet_sent_empty io descriptor p1 Q1),OUTPUT_EMPTY,
          (gateway_pending_sent_empty io descriptor p3 PENDING).
        change(gateway_sent_bytes io descriptor p4=[]);apply gateway_quiet_sent_empty;exact Q4.
      * exact SUFFIX.
Qed.
End Source.
