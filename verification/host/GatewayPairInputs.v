(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Raw private output authority becomes initialized endpoints at the actual socketpair return. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayStreamInterface GatewayThreadRuntime
  GatewaySpawnResources GatewaySpawnRuntime GatewayPairContext GatewayPairHistory.
Open Scope Z_scope.

Definition gateway_pair_input {World}native_private(discipline:option val->mem->World->Prop)
    (resources:World->gateway_resource_state)object offset(memory:mem)(world:World):Prop:=
  discipline None memory world /\native_private world object /\gateway_pair_output_cells memory object offset /\
  gateway_resource_valid(resources world).

Theorem gateway_pair_input_ambient {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)object offset:
  gateway_runtime_discipline backend(gateway_pair_input native_private discipline resources object offset).
Proof.
  intros before world after next[SIDE[PRIVATE[CELLS VALID]]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next SIDE INTERFERENCE)as[NORMAL[ACCESS MEMORY]].
  destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next SIDE VALID INTERFERENCE)as[AFTER REST].
  split;[exact NORMAL|]. split.
  - apply(proj1 ACCESS);[exact(proj1(proj2(proj2(proj1 CELLS))))|exact PRIVATE].
  - split;[|exact AFTER]. eapply gateway_pair_output_cells_unchanged;[exact CELLS|].
    eapply gateway_native_frame_restrict;[exact MEMORY| |].
    + intros block position[SAME RANGE];subst block;left;exact PRIVATE.
    + intros block position RANGE FALSE;exact FALSE.
Qed.

Theorem gateway_pair_input_reference_ambient {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    object offset origin:
  gateway_runtime_discipline backend(fun memory world=>
    gateway_pair_input native_private discipline resources object offset memory world /\
    gateway_resource_reference origin(resources world)).
Proof.
  intros before world after next[INPUT REFERENCE]INTERFERENCE;split.
  - eapply gateway_pair_input_ambient;eassumption.
  - destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next(proj1 INPUT)
      (proj2(proj2(proj2 INPUT)))INTERFERENCE)as[VALID[FRAME[STATUS EXCLUSIVE]]].
    eapply gateway_resource_reference_step;[exact REFERENCE|exact FRAME|intros;tauto|exact STATUS|exact EXCLUSIVE].
Qed.

Theorem gateway_pair_created_context {World}native_private stable_readonly discipline resources ipc object offset
    before world after next(receipt:gateway_socketpair_receipt ipc(resources world)(resources next)):
  @gateway_pair_input World native_private discipline resources object offset before world->
  discipline None after next->gateway_resource_valid(resources next)->
  gateway_access_retained native_private stable_readonly before world next->
  gateway_native_permissions before after object offset 8->
  gateway_exclusive_kept(resources world)(resources next)->
  Mem.load Mint32 after object(Ptrofs.unsigned offset)=Some(Vint(Int.repr(gateway_pair_left _ _ _ receipt)))->
  Mem.load Mint32 after object(Ptrofs.unsigned offset+4)=Some(Vint(Int.repr(gateway_pair_right _ _ _ receipt)))->
  gateway_pair_context native_private discipline resources ipc
    (gateway_pair_receipt_identity ipc(resources world)(resources next)receipt)object offset
    (gateway_pair_left _ _ _ receipt)(gateway_pair_right _ _ _ receipt)after next.
Proof.
  intros[SIDE[PRIVATE[CELLS VALID]]]NORMAL AFTER ACCESS PERMISSIONS EXCLUSIVE LEFT RIGHT.
  split;[exact NORMAL|]. split.
  - apply(proj1 ACCESS);[exact(proj1(proj2(proj2(proj1 CELLS))))|exact PRIVATE].
  - split.
    + split;[eapply gateway_pair_output_cells_permissions;eassumption|auto].
    + apply gateway_pair_receipt_resources;assumption.
Qed.
