(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Packet stores retain actual runtime and caller-owned resources. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime
  GatewayWordsMemory GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Record gateway_header_resources {World}
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)mode object held readonly original origin memory world :Prop:={
  gateway_header_thread:discipline mode memory world;
  gateway_header_private:native_private world object;
  gateway_header_live:Mem.valid_block memory object;
  gateway_header_held:forall other,In other held->Mem.valid_block memory other /\native_private world other;
  gateway_header_readonly:forall other position,readonly other position->
    Mem.perm memory other position Cur Readable /\
      (native_private world other \/stable_readonly world other position);
  gateway_header_frame:Mem.unchanged_on readonly original memory;
  gateway_header_permissions:forall position kind permission,
    Mem.perm original object position kind permission<->Mem.perm memory object position kind permission;
  gateway_header_native:gateway_native_reference native_private original origin memory world;
  gateway_header_stable:forall other position,Mem.perm original other position Cur Readable->
    stable_readonly origin other position->
    Mem.perm memory other position Cur Readable /\stable_readonly world other position
}.

Definition gateway_header_stage {World}
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)mode object held readonly original origin offset width written memory world :=
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin memory world /\
  gateway_bytes_ready object offset width written memory.

Section HeaderRuntime.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

Lemma gateway_header_resources_ambient mode object held readonly original origin before world after next :
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin before world ->
  gateway_interference backend before world after next ->
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin after next /\
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after.
Proof.
  intros RESOURCES INTERFERENCE.
  destruct RESOURCES as[SIDE PRIVATE LIVE HELD READONLY FRAME PERMISSIONS NATIVE STABLE].
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
    as[NEXT_SIDE[[RETAIN_NATIVE RETAIN_STABLE]STEP_FRAME]].
  assert(READ_FRAME:Mem.unchanged_on readonly before after).
  { eapply gateway_native_frame_restrict;[exact STEP_FRAME| |intros;unfold gateway_native_no_output;tauto].
    intros other position READ;exact(proj2(READONLY other position READ)). }
  split;[|exact STEP_FRAME];constructor.
  - exact NEXT_SIDE.
  - apply RETAIN_NATIVE;assumption.
  - eapply Mem.valid_block_unchanged_on;eassumption.
  - intros other MEMBER;destruct(HELD other MEMBER)as[OTHER_LIVE OTHER_PRIVATE];split.
    + eapply Mem.valid_block_unchanged_on;eassumption.
    + apply RETAIN_NATIVE;assumption.
  - intros other position READ;destruct(READONLY other position READ)as[READABLE CAPABILITY];split.
    + eapply Mem.perm_unchanged_on;eassumption.
    + destruct CAPABILITY as[CAPABILITY|CAPABILITY].
      * left;apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;exact READABLE|exact CAPABILITY].
      * right;apply RETAIN_STABLE;assumption.
  - eapply Mem.unchanged_on_trans;eassumption.
  - intros position kind permission;rewrite PERMISSIONS.
    apply(Mem.unchanged_on_perm _ _ _ STEP_FRAME object position kind permission);
      [split;[left;exact PRIVATE|unfold gateway_native_no_output;tauto]|exact LIVE].
  - eapply gateway_native_reference_transitive;[exact NATIVE|].
    eapply gateway_native_reference_operation;[split;eassumption|exact STEP_FRAME].
  - intros other position READABLE IMMUTABLE.
    destruct(STABLE other position READABLE IMMUTABLE)as[CURRENT_READABLE CURRENT_STABLE];split.
    + eapply Mem.perm_unchanged_on;[exact STEP_FRAME| |exact CURRENT_READABLE].
      split;[right;exact CURRENT_STABLE|unfold gateway_native_no_output;tauto].
    + apply RETAIN_STABLE;assumption.
Qed.

Lemma gateway_header_stage_ambient mode object held readonly original origin offset width written :
  gateway_ambient_closed backend
    (gateway_header_stage native_private stable_readonly discipline mode object held readonly original origin offset width written).
Proof.
  intros before world after next[RESOURCES READY]INTERFERENCE.
  destruct(gateway_header_resources_ambient _ _ _ _ _ _ _ _ _ _ RESOURCES INTERFERENCE)as[NEXT FRAME].
  split;[exact NEXT|]. eapply gateway_bytes_ready_closed;[exact READY|].
  eapply gateway_native_frame_restrict;[exact FRAME| |intros;unfold gateway_native_no_output;tauto].
  intros other position[SAME RANGE];subst other;left;exact(gateway_header_private _ _ _ _ _ _ _ _ _ _ _ RESOURCES).
Qed.

Lemma gateway_header_resources_store mode object held readonly original origin before world after offset value :
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin before world ->
  ~readonly object offset ->Mem.store Mint8unsigned before object offset(Vint value)=Some after ->
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin after world.
Proof.
  intros[SIDE PRIVATE LIVE HELD READONLY FRAME PERMISSIONS NATIVE STABLE]DISJOINT STORE.
  assert(STORE_FRAME:Mem.unchanged_on readonly before after).
  { eapply Mem.store_unchanged_on;[exact STORE|]. intros position RANGE READ;
      cbn[size_chunk]in RANGE;assert(position=offset)by lia;subst position;contradiction. }
  constructor.
  - eapply gateway_thread_native_store;eassumption.
  - exact PRIVATE.
  - eapply Mem.store_valid_block_1;eassumption.
  - intros other MEMBER;destruct(HELD other MEMBER)as[OTHER_LIVE OTHER_PRIVATE];split;
      [eapply Mem.store_valid_block_1;eassumption|exact OTHER_PRIVATE].
  - intros other position READ;destruct(READONLY other position READ)as[READABLE CAPABILITY];split;
      [eapply Mem.perm_store_1;eassumption|exact CAPABILITY].
  - eapply Mem.unchanged_on_trans;eassumption.
  - intros position kind permission;rewrite PERMISSIONS;split;
      [eapply Mem.perm_store_1;eassumption|eapply Mem.perm_store_2;eassumption].
  - intros other OTHER_LIVE OTHER_PRIVATE;destruct(NATIVE other OTHER_LIVE OTHER_PRIVATE)as[CURRENT_LIVE CURRENT_PRIVATE];split;
      [eapply Mem.store_valid_block_1;eassumption|exact CURRENT_PRIVATE].
  - intros other position READABLE IMMUTABLE;destruct(STABLE other position READABLE IMMUTABLE)as[CURRENT_READABLE CURRENT_STABLE];
      split;[eapply Mem.perm_store_1;eassumption|exact CURRENT_STABLE].
Qed.

Lemma gateway_header_stage_store mode object held readonly original origin offset width written memory world value :
  (forall position,offset<=position<offset+Z.of_nat width->~readonly object position) ->
  gateway_header_stage native_private stable_readonly discipline mode object held readonly original origin offset width written memory world ->
  (length written<width)%nat ->Int.zero_ext 8 value=value ->
  exists after,Mem.store Mint8unsigned memory object(offset+Z.of_nat(length written))(Vint value)=Some after /\
    gateway_header_stage native_private stable_readonly discipline mode object held readonly original origin offset width
      (written++[value])after world.
Proof.
  intros DISJOINT[RESOURCES READY]SPACE BYTE.
  destruct(gateway_bytes_store object offset width written memory value READY SPACE BYTE)as[after[STORE NEXT]].
  exists after;split;[exact STORE|];split;[|exact NEXT].
  eapply gateway_header_resources_store;[exact RESOURCES| |exact STORE].
  apply DISJOINT;apply Nat2Z.inj_lt in SPACE;lia.
Qed.

End HeaderRuntime.

Lemma gateway_header_resources_initial {World}native_private stable_readonly discipline mode object held readonly memory world :
  @discipline mode memory world->native_private world object->Mem.valid_block memory object->
  (forall other,In other held->Mem.valid_block memory other /\native_private world other)->
  (forall other position,readonly other position->Mem.perm memory other position Cur Readable /\
    (native_private world other \/stable_readonly world other position))->
  @gateway_header_resources World native_private stable_readonly discipline mode object held readonly memory world memory world.
Proof.
  intros SIDE PRIVATE LIVE HELD READONLY;constructor;try assumption.
  - apply Mem.unchanged_on_refl.
  - intros;reflexivity.
  - apply gateway_native_reference_refl.
  - intros;split;assumption.
Qed.
