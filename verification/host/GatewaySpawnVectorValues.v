(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The initialized source slots denote exactly the fixed launch arguments. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewaySpawnVectors GatewaySpawnVectorMemory GatewayVectorCells GatewaySpawnProcess
  GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_spawn_vectors_from_cells memory blocks symbols engine_bytes :
  Forall (gateway_vector_loaded memory) (gateway_spawn_cell_plan blocks symbols) ->
  gateway_error_cstring memory (Vptr (spawn_engine_symbol symbols) Ptrofs.zero) engine_bytes ->
  gateway_error_cstring memory (Vptr (spawn_path_symbol symbols) Ptrofs.zero) spawn_path_bytes ->
  gateway_error_cstring memory (Vptr (spawn_locale_symbol symbols) Ptrofs.zero) spawn_locale_bytes ->
  gateway_spawn_vector memory (Vptr (spawn_arguments_block blocks) Ptrofs.zero) [engine_bytes] /\
  gateway_spawn_vector memory (Vptr (spawn_environment_block blocks) Ptrofs.zero) [spawn_path_bytes; spawn_locale_bytes].
Proof.
  intros LOADED ENGINE PATH LOCALE.
  assert (SELECTED : forall cell, In cell (gateway_spawn_cell_plan blocks symbols) -> gateway_vector_loaded memory cell).
  { rewrite Forall_forall in LOADED; exact LOADED. }
  split.
  - exists (spawn_arguments_block blocks), Ptrofs.zero, [Vptr (spawn_engine_symbol symbols) Ptrofs.zero].
    split; [reflexivity |]. split; [change (16 <= 18446744073709551616); lia |]. split.
    + split.
      * apply (SELECTED (spawn_pointer_cell (spawn_arguments_block blocks) 0
          (Vptr (spawn_engine_symbol symbols) Ptrofs.zero))); cbn; tauto.
      * apply (SELECTED (spawn_pointer_cell (spawn_arguments_block blocks) 8 Vnullptr)); cbn; tauto.
    + constructor; [exact ENGINE |constructor].
  - exists (spawn_environment_block blocks), Ptrofs.zero,
      [Vptr (spawn_path_symbol symbols) Ptrofs.zero; Vptr (spawn_locale_symbol symbols) Ptrofs.zero].
    split; [reflexivity |]. split; [change (24 <= 18446744073709551616); lia |]. split.
    + split.
      * apply (SELECTED (spawn_pointer_cell (spawn_environment_block blocks) 0
          (Vptr (spawn_path_symbol symbols) Ptrofs.zero))); cbn; tauto.
      * split.
        -- apply (SELECTED (spawn_pointer_cell (spawn_environment_block blocks) 8
            (Vptr (spawn_locale_symbol symbols) Ptrofs.zero))); cbn; tauto.
        -- apply (SELECTED (spawn_pointer_cell (spawn_environment_block blocks) 16 Vnullptr)); cbn; tauto.
    + constructor; [exact PATH |]. constructor; [exact LOCALE |constructor].
Qed.
