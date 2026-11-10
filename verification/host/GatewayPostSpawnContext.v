(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Post-spawn cleanup retains caller leases without OFD exclusivity. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface GatewayOperations
  GatewayCallerBuffers GatewayCallerFamily GatewaySDKContext GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions
  GatewayPairContext GatewayReadContext GatewaySDKInputs.
Import ListNotations.
Open Scope Z_scope.

Record gateway_postspawn_context {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(resources:World->gateway_resource_state)
    (builders:World->gateway_spawn_builders)(genuine:mem->World->Prop)
    readonly selected reference owner data control data_left data_right control_left control_right
    (expected:gateway_spawn_builders)(leases:list(Z*gateway_resource_descriptor))memory world:Prop:={
  gateway_postspawn_side:discipline None memory world;
  gateway_postspawn_valid:gateway_resource_valid(resources world);
  gateway_postspawn_genuine:genuine memory world;
  gateway_postspawn_builders:builders world=expected;
  gateway_postspawn_family:gateway_caller_family native stable readonly selected reference owner memory world;
  gateway_postspawn_data:gateway_pair_cells memory data Ptrofs.zero data_left data_right;
  gateway_postspawn_control:gateway_pair_cells memory control Ptrofs.zero control_left control_right;
  gateway_postspawn_leases:Forall(fun entry=>gateway_owned_descriptor(resources world)(fst entry)(snd entry))leases
}.

Section Context.
Context {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(resources:World->gateway_resource_state)
  (builders:World->gateway_spawn_builders)(genuine:mem->World->Prop).
Variables(readonly:Values.block->Z->Prop)(selected:Values.block->Prop)(reference:mem)(owner:World)
  (data control:Values.block)(data_left data_right control_left control_right:Z).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control).
Local Definition context:=gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
  data control data_left data_right control_left control_right.

Lemma gateway_postspawn_no_output expected leases before world after next:
  context expected leases before world->discipline None after next->gateway_resource_valid(resources next)->
  genuine after next->builders next=builders world->gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_resource_frame(resources world)(resources next)(fun _=>False)(fun _=>False)->
  context expected leases after next.
Proof.
  intros[SIDE VALID GENUINE BUILDERS FAMILY DATA CONTROL LEASES]NORMAL VALID_AFTER GENUINE_AFTER SHADOW ACCESS FRAME RESOURCES.
  constructor;try assumption.
  - rewrite SHADOW;exact BUILDERS.
  - intros object MEMBER;eapply gateway_caller_buffers_no_output;[exact(FAMILY object MEMBER)|exact ACCESS|exact FRAME].
  - eapply gateway_pair_cells_unchanged;[exact DATA|].
    eapply gateway_native_frame_restrict;[exact FRAME| |intros object position HERE BAD;exact BAD].
    intros object position[SAME INSIDE];subst object;left;exact(proj1(proj2(FAMILY data DATA_SELECTED))).
  - eapply gateway_pair_cells_unchanged;[exact CONTROL|].
    eapply gateway_native_frame_restrict;[exact FRAME| |intros object position HERE BAD;exact BAD].
    intros object position[SAME INSIDE];subst object;left;exact(proj1(proj2(FAMILY control CONTROL_SELECTED))).
  - eapply Forall_impl;[|exact LEASES];intros[fd entry]OLD;eapply(proj1 RESOURCES);[exact OLD|tauto].
Qed.

Lemma gateway_postspawn_output expected changed leases before world after next object offset width:
  context expected leases before world->object<>data->object<>control->(forall position,~readonly object position)->
  discipline None after next->gateway_resource_valid(resources next)->genuine after next->builders next=changed->
  gateway_access_retained native stable before world next->gateway_native_permissions before after object offset width->
  gateway_native_frame native stable(gateway_native_region object offset width)world before after->
  gateway_resource_frame(resources world)(resources next)(fun _=>False)(fun _=>False)->
  context changed leases after next.
Proof.
  intros[SIDE VALID GENUINE BUILDERS FAMILY DATA CONTROL LEASES]AWAY_DATA AWAY_CONTROL DISJOINT
    NORMAL VALID_AFTER GENUINE_AFTER SHADOW ACCESS PERMISSIONS FRAME RESOURCES.
  constructor;try assumption.
  - eapply gateway_caller_family_output;[exact FAMILY|exact DISJOINT|exact ACCESS|exact PERMISSIONS|exact FRAME].
  - eapply gateway_pair_cells_unchanged;[exact DATA|].
    eapply gateway_native_frame_restrict;[exact FRAME| |].
    + intros other position[SAME INSIDE];subst other;left;exact(proj1(proj2(FAMILY data DATA_SELECTED))).
    + intros other position[SAME INSIDE][OUTPUT WRITTEN];congruence.
  - eapply gateway_pair_cells_unchanged;[exact CONTROL|].
    eapply gateway_native_frame_restrict;[exact FRAME| |].
    + intros other position[SAME INSIDE];subst other;left;exact(proj1(proj2(FAMILY control CONTROL_SELECTED))).
    + intros other position[SAME INSIDE][OUTPUT WRITTEN];congruence.
  - eapply Forall_impl;[|exact LEASES];intros[fd entry]OLD;eapply(proj1 RESOURCES);[exact OLD|tauto].
Qed.
Lemma gateway_postspawn_kept expected leases retained before world after next removed added:
  context expected leases before world->discipline None after next->gateway_resource_valid(resources next)->
  genuine after next->builders next=builders world->gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_resource_frame(resources world)(resources next)removed added->
  (forall entry,In entry retained->In entry leases /\~removed(fst entry))->
  context expected retained after next.
Proof.
  intros[SIDE VALID GENUINE BUILDERS FAMILY DATA CONTROL LEASES]NORMAL VALID_AFTER GENUINE_AFTER SHADOW ACCESS FRAME RESOURCES KEPT.
  constructor;try assumption.
  - rewrite SHADOW;exact BUILDERS.
  - intros object MEMBER;eapply gateway_caller_buffers_no_output;[exact(FAMILY object MEMBER)|exact ACCESS|exact FRAME].
  - eapply gateway_pair_cells_unchanged;[exact DATA|].
    eapply gateway_native_frame_restrict;[exact FRAME| |intros object position HERE BAD;exact BAD].
    intros object position[SAME INSIDE];subst object;left;exact(proj1(proj2(FAMILY data DATA_SELECTED))).
  - eapply gateway_pair_cells_unchanged;[exact CONTROL|].
    eapply gateway_native_frame_restrict;[exact FRAME| |intros object position HERE BAD;exact BAD].
    intros object position[SAME INSIDE];subst object;left;exact(proj1(proj2(FAMILY control CONTROL_SELECTED))).
  - apply Forall_forall;intros[fd entry]HERE;destruct(KEPT(fd,entry)HERE)as[MEMBER PRESENT].
    apply(proj1 RESOURCES fd entry);[exact((proj1(Forall_forall _ _))LEASES(fd,entry)MEMBER)|exact PRESENT].
Qed.

End Context.

Theorem gateway_postspawn_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources ipc
    builders genuine footprint(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint)
    readonly selected reference owner data control data_left data_right control_left control_right expected leases:
  selected data->selected control->gateway_ambient_closed backend
    (gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
      data control data_left data_right control_left control_right expected leases).
Proof.
  intros DATA_SELECTED CONTROL_SELECTED before world after next READY INTERFERENCE.
  destruct READY as[SIDE VALID GENUINE BUILDERS FAMILY DATA CONTROL LEASES].
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next SIDE INTERFERENCE)as[NORMAL[ACCESS FRAME]].
  destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next SIDE VALID INTERFERENCE)
    as[VALID_AFTER[RESOURCES REST]].
  destruct(gateway_builder_ambient _ _ _ _ _ _ _ _ _ sdk before world after next SIDE GENUINE INTERFERENCE)as[SHADOW GENUINE_AFTER].
  eapply gateway_postspawn_no_output with(before:=before)(world:=world);[exact DATA_SELECTED|exact CONTROL_SELECTED
    |constructor;assumption|exact NORMAL|exact VALID_AFTER|exact GENUINE_AFTER|exact SHADOW|exact ACCESS|exact FRAME|exact RESOURCES].
Qed.
