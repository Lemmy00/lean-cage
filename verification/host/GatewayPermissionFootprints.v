(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Actual read, SDK and allocator footprints refine the
   allocation-lifetime permission law without asserting successful source cleanup. *)
From Stdlib Require Import ZArith Classical_Prop.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayThreadRuntime GatewayStreamInterface
  GatewayNativeMemory GatewayPermissionScopes GatewayPermissionEffects GatewayPermissionSurvival.

Definition gateway_cell_permission_survival before after object position:Prop:=
  (forall kind permission,Mem.perm before object position kind permission<->Mem.perm after object position kind permission) \/
  (forall kind permission,~Mem.perm after object position kind permission).

Theorem gateway_native_footprint_cell {World}native stable output world before after object position:
  @gateway_native_frame World native stable output world before after->
  (native world object \/stable world object position)->Mem.valid_block before object->
  (output object position->gateway_cell_permission_survival before after object position)->
  gateway_cell_permission_survival before after object position.
Proof.
  intros FRAME PRIVATE LIVE OUTPUT;destruct(Classical_Prop.classic(output object position))as[WRITTEN|QUIET];[apply OUTPUT;exact WRITTEN|].
  left;intros;exact(Mem.unchanged_on_perm _ _ _ FRAME object position kind permission(conj PRIVATE QUIET)LIVE).
Qed.

Theorem gateway_python_footprint_cell python before after object position:
  python_private_frame python before after->gateway_native_private python object->Mem.valid_block before object->
  gateway_cell_permission_survival before after object position.
Proof.
  intros FRAME PRIVATE LIVE;left;intros;exact(Mem.unchanged_on_perm _ _ _ FRAME object position kind permission PRIVATE LIVE).
Qed.

Theorem gateway_constructor_permission_cell python heap before result next next_heap after description object position:
  gateway_constructor_return python heap before result next next_heap after description->
  gateway_native_private python object->Mem.valid_block before object->gateway_cell_permission_survival before after object position.
Proof. intros EFFECT PRIVATE LIVE;eapply gateway_python_footprint_cell;[exact(gateway_constructor_native _ _ _ _ _ _ _ _ EFFECT)|assumption|assumption]. Qed.
Theorem gateway_reference_permission_cell python heap before released next next_heap after object position:
  gateway_reference_return python heap before released next next_heap after->
  gateway_native_private python object->Mem.valid_block before object->gateway_cell_permission_survival before after object position.
Proof. intros EFFECT PRIVATE LIVE;eapply gateway_python_footprint_cell;[exact(gateway_reference_native _ _ _ _ _ _ _ EFFECT)|assumption|assumption]. Qed.

Theorem gateway_read_permission_cell {Event}io before stream_block stream_offset initial data_block data_offset amount readonly events after bytes object position:
  @gateway_read_receipt Event io before stream_block stream_offset initial data_block data_offset amount readonly events after bytes->
  gateway_permission_region stream_block stream_offset readonly object position->Mem.valid_block before object->
  gateway_cell_permission_survival before after object position.
Proof.
  intros RECEIPT MEMBER LIVE;left;intros;apply(gateway_permission_cells _ _ _
    (gateway_permission_read_receipt _ _ _ _ _ _ _ _ _ _ _ _ RECEIPT)object position kind permission);assumption.
Qed.

Theorem gateway_free_permission_cell {World Event}(backend:gateway_backend World Event)io native stable discipline heap_allocation
    (runtime:gateway_native_memory_runtime backend io native stable discipline heap_allocation)
    mode before world allocation amount result after next observed object position:
  discipline mode before world->native world allocation->heap_allocation allocation amount->gateway_heap_block before allocation amount->
  gateway_memory_operation backend gateway_free_api(Values.Vptr allocation Integers.Ptrofs.zero::nil)before world result after next observed->
  (native world object \/stable world object position)->Mem.valid_block before object->
  gateway_cell_permission_survival before after object position.
Proof.
  intros SIDE ALLOCATION ORIGIN HEAP OPERATION PRIVATE LIVE.
  destruct(gateway_free_operation _ _ _ _ _ _ runtime mode before world allocation amount result after next observed
    SIDE ALLOCATION ORIGIN HEAP OPERATION)as[RESULT[NEXT[ACCESS[FRAME[FREED[REVOKED IO]]]]]].
  eapply gateway_native_footprint_cell;[exact FRAME|exact PRIVATE|exact LIVE|].
  intros[SAME RANGE];subst object;right;intros;eapply REVOKED;exact RANGE.
Qed.
