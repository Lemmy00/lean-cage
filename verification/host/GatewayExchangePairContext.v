(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Actual pair births and normalized cells retain one caller's history. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources
  GatewayPairSource GatewayPairContext GatewayPairInputs GatewayPairHistory GatewayPairActual GatewayPairBuffers
  GatewayCallerBuffers GatewayCallerFamily GatewayBufferReference GatewayExchangeContext GatewayExchangeSetup
  GatewayThreadRuntime GatewayStreamInterface GatewayCallerClockResources.
Import ListNotations.

Definition gateway_pair_birth_in_run {World Event}(backend:gateway_backend World Event)
    (resources:World->gateway_resource_state)ipc object before world events after next(identity:gateway_pair_identity ipc):Prop:=
  exists prefix suffix called call_world born born_world observed
    (receipt:gateway_socketpair_receipt ipc(resources call_world)(resources born_world)),
    identity=gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt /\
    events=prefix++gateway_primitive observed::suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object Ptrofs.zero]Kstop before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object Ptrofs.zero)
        (pair_socket_cont(Vptr object Ptrofs.zero))called)call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api(pair_socket_arguments object Ptrofs.zero)
      called call_world(Vint Int.zero)born born_world observed /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(pair_socket_cont(Vptr object Ptrofs.zero))born)born_world)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).

Lemma gateway_caller_family_pair_input {World}native stable discipline(resources:World->gateway_resource_state)
    readonly selected reference owner original before world object:
  gateway_exchange_context native stable discipline resources readonly selected reference owner original before world->
  selected object->Mem.range_perm reference object 0 8 Cur Freeable->
  gateway_pair_input native discipline resources object Ptrofs.zero before world.
Proof.
  intros[SIDE[[VALID HISTORY]FAMILY]]SELECTED PERMISSIONS.
  destruct(FAMILY object SELECTED)as[LIVE[PRIVATE[READONLY[[FRAME CURRENT]REST]]]].
  split;[exact SIDE|]. split;[exact PRIVATE|]. split;[|exact VALID].
  apply exchange_pair_cells_from_stack;intros position RANGE.
  apply(proj1(CURRENT object(or_introl eq_refl)position Cur Freeable));apply PERMISSIONS;exact RANGE.
Qed.

Theorem actual_exchange_pair_preserves_context_with_origin {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno resources ipc
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    readonly selected reference owner original object before world events after next:
  (forall position,~readonly object position)->selected object->Mem.range_perm reference object 0 8 Cur Freeable->
  gateway_exchange_context native stable discipline resources readonly selected reference owner original before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object Ptrofs.zero]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists(identity:gateway_pair_identity ipc)left right,
    (4<=left)%Z /\(4<=right)%Z /\gateway_pair_birth_in_run backend resources ipc object before world events after next identity /\
    gateway_resource_reference(resources world)(pair_origin ipc identity) /\
    gateway_pair_context native discipline resources ipc identity object Ptrofs.zero left right after next /\
    gateway_exchange_context native stable discipline resources readonly selected reference owner original after next.
Proof.
  intros DISJOINT SELECTED PERMISSIONS INITIAL RUN.
  pose proof(gateway_caller_family_pair_input native stable discipline resources readonly selected reference owner original
    before world object INITIAL SELECTED PERMISSIONS)as RAW.
  destruct(actual_private_pair_with_origin_history backend io native stable discipline thread_errno resources ipc thread descriptors
    object Ptrofs.zero(gateway_caller_family native stable readonly selected reference owner)
    (gateway_caller_family_pair_laws backend io native stable discipline thread_errno thread readonly selected object
      Ptrofs.zero reference owner DISJOINT)before world events after next RAW(proj2(proj2 INITIAL))RUN)
    as(prefix&suffix&called&call_world&born&born_world&observed&receipt&EVENTS&PREFIX&OPERATION&SUFFIX&CALLED&ORIGIN&REFERENCE&
      left&right&LEFT&RIGHT&PAIR&FAMILY).
  exists(gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt),left,right.
  split;[exact LEFT|]. split;[exact RIGHT|]. split.
  - exists prefix,suffix,called,call_world,born,born_world,observed,receipt.
    split;[reflexivity|]. split;[exact EVENTS|]. split;[exact PREFIX|]. split;assumption.
  - split;[exact ORIGIN|]. split;[exact PAIR|].
    destruct PAIR as[SIDE[PRIVATE[CELLS RESOURCES]]].
    split;[exact SIDE|]. split;[|exact FAMILY]. split;[exact(proj1 RESOURCES)|].
    eapply gateway_resource_reference_transitive;[exact(proj2(proj1(proj2 INITIAL)))|exact REFERENCE].
Qed.

Theorem actual_exchange_pair_preserves_context {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno resources ipc
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    readonly selected reference owner original object before world events after next:
  (forall position,~readonly object position)->selected object->Mem.range_perm reference object 0 8 Cur Freeable->
  gateway_exchange_context native stable discipline resources readonly selected reference owner original before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object Ptrofs.zero]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists(identity:gateway_pair_identity ipc)left right,
    (4<=left)%Z /\(4<=right)%Z /\gateway_pair_birth_in_run backend resources ipc object before world events after next identity /\
    gateway_pair_context native discipline resources ipc identity object Ptrofs.zero left right after next /\
    gateway_exchange_context native stable discipline resources readonly selected reference owner original after next.
Proof.
  intros DISJOINT SELECTED PERMISSIONS INITIAL RUN.
  destruct(actual_exchange_pair_preserves_context_with_origin backend io native stable discipline thread_errno resources ipc thread descriptors
    readonly selected reference owner original object before world events after next DISJOINT SELECTED PERMISSIONS INITIAL RUN)
    as(identity&left&right&LEFT&RIGHT&BIRTH&ORIGIN&PAIR&CONTEXT).
  exists identity,left,right;split;[exact LEFT|]. split;[exact RIGHT|]. split;[exact BIRTH|]. split;assumption.
Qed.
