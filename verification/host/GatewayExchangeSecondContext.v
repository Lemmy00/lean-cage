(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: A real second pair preserves the first pair's cells and object births. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnRuntime GatewaySpawnResources
  GatewayPairContext GatewaySpawnTopology GatewayPairHistory GatewayPairReference GatewayExchangePairContext GatewayExchangeContext
  GatewayCallerBuffers GatewayCallerFamily GatewayCallerRetention GatewayCallerClockResources GatewayBufferReference
  GatewayThreadRuntime GatewayStreamInterface GatewayOperations.
Import ListNotations.

Lemma gateway_caller_family_current_range {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    readonly selected reference owner before world object low high kind permission:
  gateway_caller_family native stable readonly selected reference owner before world->selected object->
  Mem.range_perm reference object low high kind permission->Mem.range_perm before object low high kind permission.
Proof.
  intros FAMILY SELECTED PERMISSIONS.
  destruct(FAMILY object SELECTED)as[LIVE[PRIVATE[READONLY[[FRAME CURRENT]REST]]]].
  intros position RANGE;apply(proj1(CURRENT object(or_introl eq_refl)position kind permission));apply PERMISSIONS;exact RANGE.
Qed.

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
    gateway_pair_birth_in_run backend resources ipc control before world events after next second /\
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
  destruct(actual_exchange_pair_preserves_context_with_origin backend io native stable discipline thread_errno resources ipc thread descriptors
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
Theorem actual_exchange_second_pair_preserves_first(identity:gateway_pair_identity ipc)left right data control
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
    gateway_pair_birth_in_run backend resources ipc control before world events after next second /\
    gateway_pair_context native discipline resources ipc second control Ptrofs.zero second_left second_right after next /\
    gateway_pair_context native discipline resources ipc identity data Ptrofs.zero left right after next /\
    gateway_exchange_context native stable discipline resources readonly selected reference owner original after next.
Proof.
  intros SEPARATE DATA_SELECTED CONTROL_SELECTED READONLY_SEPARATE PERMISSIONS FIRST INITIAL RUN.
  destruct(actual_exchange_second_pair_preserves_first_separate identity left right data control before world events after next
    SEPARATE DATA_SELECTED CONTROL_SELECTED READONLY_SEPARATE PERMISSIONS FIRST INITIAL RUN)
    as(second&second_left&second_right&LEFT&RIGHT&BIRTH&OBJECTS&SECOND&RETAINED&CONTEXT).
  exists second,second_left,second_right;split;[exact LEFT|]. split;[exact RIGHT|]. split;[exact BIRTH|].
  split;[exact SECOND|]. split;assumption.
Qed.

End SecondContext.
