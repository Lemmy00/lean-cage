(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Pair source scripts use derived single-operation caller-buffer adapters. *)
From Stdlib Require Import ZArith.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayThreadRuntime GatewayCallerBuffers.
From HostGateway Require Import GatewaySpawnResources GatewaySpawnRuntime GatewayPairContext GatewayFramedRuntime.
Open Scope Z_scope.

Record gateway_pair_buffer_laws {World Event}(backend:gateway_backend World Event)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)object offset(history:mem->World->Prop):Prop:={
  gateway_pair_buffer_ambient:forall before world after next,
    discipline None before world->history before world->gateway_interference backend before world after next->history after next;
  gateway_pair_buffer_no_output:forall before world after next,
    history before world->gateway_access_retained native_private stable_readonly before world next->
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after->history after next;
  gateway_pair_buffer_socket:forall before world after next,
    history before world->gateway_access_retained native_private stable_readonly before world next->
    gateway_native_permissions before after object offset 8->
    gateway_native_frame native_private stable_readonly(gateway_native_region object offset 8)world before after->history after next;
  gateway_pair_buffer_store:forall before world after position value,
    history before world->Mem.store Mint32 before object position value=Some after->history after world
}.

Lemma gateway_native_region_dec object offset count:
  forall block position,{gateway_native_region object offset count block position}+{~gateway_native_region object offset count block position}.
Proof.
  intros block position;unfold gateway_native_region.
  destruct(peq block object)as[SAME|DIFFERENT];[subst block|right;tauto].
  destruct(Z_le_dec(Ptrofs.unsigned offset)position)as[LOW|LOW];[|right;tauto].
  destruct(Z_lt_dec position(Ptrofs.unsigned offset+count))as[HIGH|HIGH];[left;auto|right;tauto].
Qed.

Theorem gateway_pair_caller_buffer_laws {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    readonly object offset reference owner:
  (forall position,~readonly object position)->
  gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset
    (gateway_caller_buffers native_private stable_readonly readonly object reference owner).
Proof.
  intro DISJOINT;constructor.
  - intros before world after next SIDE HISTORY INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next SIDE INTERFERENCE)
      as[NORMAL[ACCESS FRAME]]. eapply gateway_caller_buffers_no_output;eassumption.
  - intros before world after next HISTORY ACCESS FRAME;eapply gateway_caller_buffers_no_output;eassumption.
  - intros before world after next HISTORY ACCESS PERMISSIONS FRAME.
    eapply gateway_caller_buffers_operation;[exact HISTORY|exact ACCESS|exact FRAME|apply gateway_native_region_dec| | |].
    + intros block position HERE[SAME RANGE];subst block;exact(DISJOINT position HERE).
    + intros position kind permission[SAME RANGE];apply PERMISSIONS;exact RANGE.
    + intros block position READABLE[SAME RANGE];subst block;apply(proj1(PERMISSIONS position Cur Readable RANGE));exact READABLE.
  - intros before world after position value HISTORY STORE;eapply gateway_caller_buffers_store;
      [exact HISTORY|exact STORE|exact DISJOINT].
Qed.

Theorem gateway_pair_trivial_buffer_laws {World Event}(backend:gateway_backend World Event)native_private stable_readonly discipline object offset:
  gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset(fun _ _=>True).
Proof. constructor;intros;exact I. Qed.

Definition gateway_pair_full_context {World}native_private discipline resources ipc(identity:gateway_pair_identity ipc)
    object offset left right(history:mem->World->Prop)(memory:mem)(world:World):Prop:=
  gateway_pair_context native_private discipline resources ipc identity object offset left right memory world /\history memory world.
Definition gateway_pair_full_storage {World}native_private discipline resources ipc(identity:gateway_pair_identity ipc)
    object offset stored_left stored_right left right(history:mem->World->Prop)(memory:mem)(world:World):Prop:=
  gateway_pair_storage_context native_private discipline resources ipc identity object offset stored_left stored_right left right memory world /\
    history memory world.

Theorem gateway_pair_full_context_ambient {World Event}(backend:gateway_backend World Event)io native_private stable_readonly discipline
    thread_errno resources ipc(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    (identity:gateway_pair_identity ipc)object offset left right history
    (buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history):
  gateway_ambient_closed backend(gateway_pair_full_context native_private discipline resources ipc identity object offset left right history).
Proof.
  intros before world after next[BASE HISTORY]INTERFERENCE;split.
  - eapply gateway_pair_context_ambient;eassumption.
  - eapply gateway_pair_buffer_ambient;[exact buffers|exact(proj1 BASE)|exact HISTORY|exact INTERFERENCE].
Qed.
Theorem gateway_pair_full_storage_ambient {World Event}(backend:gateway_backend World Event)io native_private stable_readonly discipline
    thread_errno resources ipc(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    (identity:gateway_pair_identity ipc)object offset stored_left stored_right left right history
    (buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history):
  gateway_ambient_closed backend(gateway_pair_full_storage native_private discipline resources ipc identity object offset
    stored_left stored_right left right history).
Proof.
  intros before world after next[BASE HISTORY]INTERFERENCE;split.
  - eapply gateway_pair_storage_ambient;eassumption.
  - eapply gateway_pair_buffer_ambient;[exact buffers|exact(proj1 BASE)|exact HISTORY|exact INTERFERENCE].
Qed.

Theorem gateway_pair_full_storage_preserved {World Event}(backend:gateway_backend World Event)native_private stable_readonly discipline
    resources ipc(identity:gateway_pair_identity ipc)object offset stored_left stored_right left right history
    (buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history)
    before world after next removed added:
  gateway_pair_full_storage native_private discipline resources ipc identity object offset stored_left stored_right left right history before world->
  discipline None after next->gateway_access_retained native_private stable_readonly before world next->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after->
  gateway_resource_valid(resources next)->gateway_resource_frame(resources world)(resources next)removed added->
  ~removed left->~removed right->gateway_resource_status_frame(resources world)(resources next)(fun _=>False)->
  (forall fd entry,gateway_owned_descriptor(pair_origin _ identity)fd entry->~removed fd)->
  gateway_exclusive_kept(resources world)(resources next)->
  gateway_pair_full_storage native_private discipline resources ipc identity object offset stored_left stored_right left right history after next.
Proof.
  intros[BASE HISTORY]NORMAL ACCESS FRAME VALID RESOURCES LEFT RIGHT STATUS ORIGINAL EXCLUSIVE;split.
  - eapply gateway_pair_storage_preserved;eassumption.
  - eapply gateway_pair_buffer_no_output;[exact buffers|exact HISTORY|exact ACCESS|exact FRAME].
Qed.
