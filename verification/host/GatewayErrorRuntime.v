(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Error posting preserves real native owners independently of pending exceptions. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime
  GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_error_cstring (memory : mem) (pointer : val) (bytes : list Byte.int) : Prop :=
  exists object offset,
    pointer = Vptr object offset /\ ~ In Byte.zero bytes /\
    Ptrofs.unsigned offset + Z.of_nat (length bytes) + 1 <= Ptrofs.modulus /\
    Mem.loadbytes memory object (Ptrofs.unsigned offset) (Z.of_nat (length bytes) + 1) =
      Some (inj_bytes (bytes ++ [Byte.zero])).

(* Rooted describes an attached interpreter and its live heap/reference roots.
   It deliberately permits a pending exception. Actual caller proofs connect
   this predicate to the normal context before entering an error branch. *)
Record gateway_error_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (normal : mem -> World -> Prop) (rooted : mem -> World -> Prop)
    (exception : World -> val -> Prop) (pending : World -> Prop) (errno_cell : World -> val -> Prop) : Prop := {
  gateway_normal_is_rooted : forall memory world, normal memory world -> rooted memory world;

  gateway_error_ambient : forall before world after next,
    rooted before world -> gateway_interference backend before world after next ->
    rooted after next /\ gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after;

  gateway_error_native_alloc : forall before world after object low high,
    rooted before world -> Mem.alloc before low high = (after, object) -> rooted after world;
  gateway_error_native_store : forall before world after object offset chunk value,
    rooted before world -> native_private world object -> Mem.store chunk before object offset value = Some after ->
    rooted after world;
  gateway_error_native_free : forall before world after object low high,
    rooted before world -> native_private world object -> Mem.free before object low high = Some after ->
    rooted after world;

  gateway_error_check_signals : forall before world result after next observed,
    normal before world -> gateway_runtime_operation backend gateway_check_signals_definition []
      before world result after next observed ->
    (exists status, result = Vint status) /\ rooted after next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    io observed = None;

  gateway_error_set_string : forall before world kind message bytes result after next observed,
    rooted before world -> exception world kind -> gateway_error_cstring before message bytes ->
    gateway_runtime_operation backend gateway_set_error_definition [kind; message]
      before world result after next observed ->
    rooted after next /\ pending next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    io observed = None;

  gateway_error_errno_location : forall before world result after next observed,
    rooted before world -> gateway_runtime_operation backend gateway_errno_location_definition []
      before world result after next observed ->
    exists object offset,
      result = Vptr object offset /\ errno_cell next result /\
      gateway_native_pointer after object offset 4 Writable /\
      rooted after next /\
      gateway_access_retained native_private stable_readonly before world next /\
      gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
      io observed = None;

  gateway_error_errno_store : forall before world after object offset number,
    rooted before world -> errno_cell world (Vptr object offset) ->
    Mem.storev Mint32 before (Vptr object offset) (Vint number) = Some after ->
    rooted after world /\ gateway_native_frame native_private stable_readonly gateway_native_no_output world before after;

  gateway_error_from_errno : forall before world kind result after next observed,
    rooted before world -> exception world kind ->
    gateway_runtime_operation backend gateway_errno_error_definition [kind]
      before world result after next observed ->
    result = Vnullptr /\ rooted after next /\ pending next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    io observed = None
}.
