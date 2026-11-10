(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Single native descriptor operations preserve actual caller owners. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewaySpawnABI GatewaySpawnResources
  GatewaySpawnDescriptors GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_pair_output_cells memory object offset : Prop :=
  gateway_native_pointer memory object offset 8 Writable /\
  Mem.valid_access memory Mint32 object (Ptrofs.unsigned offset) Writable /\
  Mem.valid_access memory Mint32 object (Ptrofs.unsigned offset + 4) Writable.

Definition gateway_exclusive_kept (before after : gateway_resource_state) : Prop :=
  forall description, gateway_resource_exclusive before description = true ->
    gateway_resource_exclusive after description = true.

Definition gateway_nonblocking_flag flags : bool := negb (Int.eq (Int.and flags (Int.repr 2048)) Int.zero).

Record gateway_spawn_descriptor_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (resources : World -> gateway_resource_state)
    (ipc : nat -> Prop) : Prop := {
  (* This one-step host-code boundary protects only actual caller leases. The
     source must first obtain those leases; unrelated FD slots remain broad. *)
  gateway_spawn_ambient : forall before world after next,
    discipline None before world -> gateway_resource_valid (resources world) ->
    gateway_interference backend before world after next ->
    gateway_resource_valid (resources next) /\
    gateway_resource_frame (resources world) (resources next) (fun _ => False) (fun _ => False) /\
    gateway_resource_status_frame (resources world) (resources next) (fun _ => False) /\
    gateway_exclusive_kept (resources world) (resources next);

  gateway_socketpair_operation : forall before world object offset result after next observed,
    discipline None before world -> gateway_resource_valid (resources world) -> native_private world object ->
    gateway_pair_output_cells before object offset ->
    gateway_spawn_operation backend gateway_socketpair_api
      [Vint Int.one; Vint (Int.repr 526337); Vint Int.zero; Vptr object offset]
      before world result after next observed ->
    discipline None after next /\ gateway_resource_valid (resources next) /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_permissions before after object offset 8 /\
    gateway_native_frame native_private stable_readonly (gateway_native_region object offset 8) world before after /\
    gateway_exclusive_kept (resources world) (resources next) /\ io observed = None /\
    ((result = Vint (Int.neg Int.one) /\
      Mem.unchanged_on (gateway_native_region object offset 8) before after /\
      gateway_resource_frame (resources world) (resources next) (fun _ => False) (fun _ => False) /\
      gateway_resource_status_frame (resources world) (resources next) (fun _ => False)) \/
     exists receipt : gateway_socketpair_receipt ipc (resources world) (resources next),
      result = Vint Int.zero /\
      Mem.load Mint32 after object (Ptrofs.unsigned offset) =
        Some (Vint (Int.repr (gateway_pair_left _ _ _ receipt))) /\
      Mem.load Mint32 after object (Ptrofs.unsigned offset + 4) =
        Some (Vint (Int.repr (gateway_pair_right _ _ _ receipt))));

  gateway_duplicate_operation : forall before world source minimum entry result after next observed,
    discipline None before world -> gateway_resource_valid (resources world) ->
    gateway_owned_descriptor (resources world) source entry -> 0 <= minimum <= Int.max_signed ->
    gateway_spawn_operation backend gateway_fcntl_api
      [Vint (Int.repr source); Vint (Int.repr 1030); Vint (Int.repr minimum)]
      before world result after next observed ->
    discipline None after next /\ gateway_resource_valid (resources next) /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    gateway_exclusive_kept (resources world) (resources next) /\ io observed = None /\
    ((result = Vint (Int.neg Int.one) /\
      gateway_resource_frame (resources world) (resources next) (fun _ => False) (fun _ => False) /\
      gateway_resource_status_frame (resources world) (resources next) (fun _ => False)) \/
     exists returned, result = Vint (Int.repr returned) /\
      gateway_duplicate_receipt (resources world) (resources next) source minimum returned entry);

  gateway_get_flags_operation : forall before world source entry result after next observed,
    discipline None before world -> gateway_resource_valid (resources world) ->
    gateway_owned_descriptor (resources world) source entry ->
    gateway_resource_exclusive (resources world) (gateway_resource_description (gateway_descriptor_object entry)) = true ->
    gateway_spawn_operation backend gateway_fcntl_api
      [Vint (Int.repr source); Vint (Int.repr 3); Vint Int.zero]
      before world result after next observed ->
    discipline None after next /\ gateway_resource_valid (resources next) /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    gateway_resource_frame (resources world) (resources next) (fun _ => False) (fun _ => False) /\
    gateway_resource_status_frame (resources world) (resources next) (fun _ => False) /\
    gateway_exclusive_kept (resources world) (resources next) /\ io observed = None /\
    (result = Vint (Int.neg Int.one) \/ exists flags, result = Vint flags /\ 0 <= Int.signed flags /\
      gateway_nonblocking_flag flags =
        gateway_resource_nonblocking (resources next) (gateway_resource_description (gateway_descriptor_object entry)));

  gateway_set_flags_operation : forall before world source entry flags result after next observed,
    discipline None before world -> gateway_resource_valid (resources world) ->
    gateway_owned_descriptor (resources world) source entry ->
    gateway_resource_exclusive (resources world) (gateway_resource_description (gateway_descriptor_object entry)) = true ->
    gateway_spawn_operation backend gateway_fcntl_api
      [Vint (Int.repr source); Vint (Int.repr 4); Vint flags]
      before world result after next observed ->
    discipline None after next /\ gateway_resource_valid (resources next) /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    gateway_resource_frame (resources world) (resources next) (fun _ => False) (fun _ => False) /\
    gateway_resource_status_frame (resources world) (resources next)
      (fun description => description = gateway_resource_description (gateway_descriptor_object entry)) /\
    gateway_exclusive_kept (resources world) (resources next) /\ io observed = None /\
    (result = Vint (Int.neg Int.one) \/ result = Vint Int.zero /\
      gateway_resource_nonblocking (resources next) (gateway_resource_description (gateway_descriptor_object entry)) =
        gateway_nonblocking_flag flags);

  (* Linux close consumes the valid owned lease even when interrupted. Another
     thread may reuse the numeric slot; no after-table absence is asserted. *)
  gateway_close_operation : forall before world source entry result after next observed,
    discipline None before world -> gateway_resource_valid (resources world) ->
    gateway_owned_descriptor (resources world) source entry ->
    gateway_spawn_operation backend gateway_close_api [Vint (Int.repr source)] before world result after next observed ->
    (result = Vint Int.zero \/ result = Vint (Int.neg Int.one)) /\
    discipline None after next /\ gateway_resource_valid (resources next) /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    gateway_resource_owned (resources next) source = false /\
    gateway_resource_frame (resources world) (resources next) (fun fd => fd = source) (fun _ => False) /\
    gateway_resource_status_frame (resources world) (resources next) (fun _ => False) /\
    gateway_exclusive_kept (resources world) (resources next) /\ io observed = None
}.

Lemma gateway_removed_nonblocking flags :
  gateway_nonblocking_flag (Int.and flags (Int.not (Int.repr 2048))) = false.
Proof.
  unfold gateway_nonblocking_flag; rewrite Int.and_assoc.
  rewrite Int.and_commut with (x := Int.not (Int.repr 2048)).
  rewrite Int.and_not_self, Int.and_zero; reflexivity.
Qed.
