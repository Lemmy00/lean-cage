(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Individual read/SDK/native effects preserve the caller's exact
   permission cells independently of permitted byte mutations and object pointer aliases. *)
From Stdlib Require Import ZArith List Classical_Prop.
From compcert Require Import Values Memory Integers.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayThreadRuntime
  GatewayStreamInterface GatewayPermissionScopes.

Definition gateway_permission_region stream_block stream_offset(readonly:block->Z->Prop)object position:Prop:=
  (object=stream_block /\Ptrofs.unsigned stream_offset<=position<Ptrofs.unsigned stream_offset+48)%Z \/readonly object position.

Theorem gateway_permission_read_receipt {Event}io before stream_block stream_offset initial data_block data_offset amount readonly events after bytes:
  @gateway_read_receipt Event io before stream_block stream_offset initial data_block data_offset amount readonly events after bytes->
  gateway_permission_frame(gateway_permission_region stream_block stream_offset readonly)before after.
Proof.
  intro RECEIPT;split.
  - intros object LIVE;eapply Mem.valid_block_unchanged_on;[exact(gateway_read_retained _ _ _ _ _ _ _ _ _ _ _ _ RECEIPT)|exact LIVE].
  - intros object position kind permission[STREAM|READONLY]LIVE.
    + destruct STREAM as[SAME RANGE];subst object;exact(gateway_read_stream_permissions _ _ _ _ _ _ _ _ _ _ _ _ RECEIPT position kind permission RANGE).
    + exact(Mem.unchanged_on_perm _ _ _(gateway_read_retained _ _ _ _ _ _ _ _ _ _ _ _ RECEIPT)object position kind permission READONLY LIVE).
Qed.

Theorem gateway_permission_native_effect {World}native stable output world protected before after:
  (forall object position,protected object position->native world object)->
  @gateway_native_frame World native stable output world before after->
  (forall object position kind permission,protected object position->output object position->Mem.valid_block before object->
    (Mem.perm before object position kind permission<->Mem.perm after object position kind permission))->
  gateway_permission_frame protected before after.
Proof.
  intros PRIVATE FRAME OUTPUT;split.
  - intros object LIVE;eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE].
  - intros object position kind permission MEMBER LIVE.
    destruct(Classical_Prop.classic(output object position))as[WRITTEN|UNTOUCHED].
    + apply OUTPUT;assumption.
    + apply(Mem.unchanged_on_perm _ _ _ FRAME object position kind permission);[split;[left;apply PRIVATE with(position:=position);exact MEMBER|exact UNTOUCHED]|exact LIVE].
Qed.

Theorem gateway_permission_native_disjoint {World}native stable output world protected before after:
  (forall object position,protected object position->native world object)->
  (forall object position,protected object position->~output object position)->
  @gateway_native_frame World native stable output world before after->gateway_permission_frame protected before after.
Proof.
  intros PRIVATE DISJOINT FRAME;eapply gateway_permission_native_effect;[exact PRIVATE|exact FRAME|].
  intros;exfalso;eapply DISJOINT;eassumption.
Qed.

Theorem gateway_permission_python_effect python protected before after:
  (forall object position,protected object position->gateway_native_private python object)->
  python_private_frame python before after->gateway_permission_frame protected before after.
Proof.
  intros PRIVATE FRAME;apply gateway_permission_unchanged;eapply Mem.unchanged_on_implies;[exact FRAME|].
  intros object position MEMBER LIVE;apply PRIVATE with(position:=position);exact MEMBER.
Qed.
