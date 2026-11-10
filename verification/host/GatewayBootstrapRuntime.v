(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Loader and string operations expose their actual bounded bytes. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapABI GatewayThreadRuntime GatewayStreamInterface GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_bytes memory pointer bytes : Prop :=
  exists object offset, pointer = Vptr object offset /\
    Ptrofs.unsigned offset + Z.of_nat (length bytes) <= Ptrofs.modulus /\
    Mem.loadbytes memory object (Ptrofs.unsigned offset) (Z.of_nat (length bytes)) = Some (map Byte bytes).

Definition gateway_bootstrap_protected {World} (native : World -> block -> Prop)
    (stable : World -> block -> Z -> Prop) memory world pointer bytes : Prop :=
  exists object offset, pointer = Vptr object offset /\
    gateway_bootstrap_bytes memory pointer bytes /\
    forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length bytes) ->
      native world object \/ stable world object position.

Definition gateway_bootstrap_disjoint (destination : block) destination_offset count (source : block) source_offset : Prop :=
  destination <> source \/ Ptrofs.unsigned destination_offset + count <= Ptrofs.unsigned source_offset \/
    Ptrofs.unsigned source_offset + count <= Ptrofs.unsigned destination_offset.

Definition gateway_bootstrap_separate_source pointer (destination : block) : Prop :=
  forall source offset, pointer = Vptr source offset -> source <> destination.

Definition gateway_bootstrap_post {World Event} (io : Event -> option gateway_native_io)
    native stable (discipline : option val -> mem -> World -> Prop)
    output before world after next observed : Prop :=
  discipline None after next /\ gateway_access_retained native stable before world next /\
  gateway_native_frame native stable output world before after /\ io observed = None.

Record gateway_bootstrap_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io) (native : World -> block -> Prop)
    (stable : World -> block -> Z -> Prop) (discipline : option val -> mem -> World -> Prop)
    (module_filename : World -> val -> list Byte.int -> Prop)
    (canonicalizes : World -> World -> list Byte.int -> list Byte.int -> Prop) : Prop := {
  gateway_loader_address_operation : forall before world address object offset result after next observed,
    discipline None before world -> native world object ->
    gateway_native_pointer before object offset 32 Writable ->
    Mem.valid_access before Mptr object (Ptrofs.unsigned offset) Writable ->
    gateway_bootstrap_operation backend gateway_loader_address_api [address; Vptr object offset]
      before world result after next observed ->
    gateway_bootstrap_post io native stable discipline (gateway_native_region object offset 32)
      before world after next observed /\ gateway_native_permissions before after object offset 32 /\
    exists status, result = Vint status /\
      (status <> Int.zero -> exists filename,
        Mem.load Mptr after object (Ptrofs.unsigned offset) = Some filename /\
        (filename = Vnullptr \/ exists bytes name name_offset,
          filename = Vptr name name_offset /\ gateway_error_cstring after filename bytes /\
          gateway_bootstrap_protected native stable after next filename (bytes ++ [Byte.zero]) /\
          ~ native next name /\ module_filename next address bytes));

  gateway_bounded_length_operation : forall before world pointer bytes maximum result after next observed,
    discipline None before world -> gateway_error_cstring before pointer bytes ->
    gateway_bootstrap_protected native stable before world pointer (bytes ++ [Byte.zero]) ->
    0 <= maximum <= Int64.max_unsigned ->
    gateway_bootstrap_operation backend gateway_bounded_length_api [pointer; Vlong (Int64.repr maximum)]
      before world result after next observed ->
    gateway_bootstrap_post io native stable discipline gateway_native_no_output before world after next observed /\
    result = Vlong (Int64.repr (Z.min maximum (Z.of_nat (length bytes))));

  gateway_memory_compare_operation : forall before world first second left right result after next observed,
    discipline None before world -> gateway_bootstrap_protected native stable before world first left ->
    gateway_bootstrap_protected native stable before world second right -> length left = length right ->
    Z.of_nat (length left) <= Int64.max_unsigned ->
    gateway_bootstrap_operation backend gateway_memory_compare_api
      [first; second; Vlong (Int64.repr (Z.of_nat (length left)))] before world result after next observed ->
    gateway_bootstrap_post io native stable discipline gateway_native_no_output before world after next observed /\
    exists status, result = Vint status /\ (status = Int.zero <-> left = right);

  gateway_memory_copy_operation : forall before world destination destination_offset source source_offset bytes
      result after next observed,
    discipline None before world -> native world destination ->
    gateway_native_pointer before destination destination_offset (Z.of_nat (length bytes)) Writable ->
    gateway_bootstrap_protected native stable before world (Vptr source source_offset) bytes ->
    gateway_bootstrap_disjoint destination destination_offset (Z.of_nat (length bytes)) source source_offset ->
    Z.of_nat (length bytes) <= Int64.max_unsigned ->
    gateway_bootstrap_operation backend gateway_memory_copy_api
      [Vptr destination destination_offset; Vptr source source_offset; Vlong (Int64.repr (Z.of_nat (length bytes)))]
      before world result after next observed ->
    gateway_bootstrap_post io native stable discipline
      (gateway_native_region destination destination_offset (Z.of_nat (length bytes))) before world after next observed /\
    gateway_native_permissions before after destination destination_offset (Z.of_nat (length bytes)) /\
    result = Vptr destination destination_offset /\
    gateway_bootstrap_bytes after (Vptr destination destination_offset) bytes;

  gateway_canonical_path_operation : forall before world pointer original destination result after next observed,
    discipline None before world -> gateway_error_cstring before pointer original ->
    gateway_bootstrap_protected native stable before world pointer (original ++ [Byte.zero]) ->
    native world destination -> gateway_native_pointer before destination Ptrofs.zero 4096 Writable ->
    gateway_bootstrap_separate_source pointer destination ->
    gateway_bootstrap_operation backend gateway_canonical_path_api [pointer; Vptr destination Ptrofs.zero]
      before world result after next observed ->
    gateway_bootstrap_post io native stable discipline (gateway_native_region destination Ptrofs.zero 4096)
      before world after next observed /\ gateway_native_permissions before after destination Ptrofs.zero 4096 /\
    (result = Vnullptr \/ exists canonical,
      result = Vptr destination Ptrofs.zero /\ Z.of_nat (length canonical) <= 4095 /\
      gateway_error_cstring after result canonical /\ canonicalizes world next original canonical)
}.
