(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: All six launch-vector cells are filled by their real C assignments. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewaySpawnVectors GatewaySpawnVectorMemory GatewayVectorCells.
Import ListNotations.
Open Scope Z_scope.

Record gateway_spawn_vector_locations (ge : Clight.genv) (environment : env) blocks symbols : Prop := {
  spawn_child_location : environment ! _child = Some (spawn_child_block blocks, tint);
  spawn_arguments_location : environment ! _arguments = Some (spawn_arguments_block blocks, tarray (tptr tschar) 2);
  spawn_environment_location : environment ! _environment = Some (spawn_environment_block blocks, tarray (tptr tschar) 3);
  spawn_engine_not_local : environment ! _host_engine = None;
  spawn_path_not_local : environment ! (spawn_vector_literal 3) = None;
  spawn_locale_not_local : environment ! (spawn_vector_literal 4) = None;
  spawn_engine_binding : Genv.find_symbol ge _host_engine = Some (spawn_engine_symbol symbols);
  spawn_path_binding : Genv.find_symbol ge (spawn_vector_literal 3) = Some (spawn_path_symbol symbols);
  spawn_locale_binding : Genv.find_symbol ge (spawn_vector_literal 4) = Some (spawn_locale_symbol symbols)
}.

Lemma spawn_global_array_reference (ge : Clight.genv) environment temporaries memory identifier ty symbol :
  environment ! identifier = None -> Genv.find_symbol ge identifier = Some symbol ->
  access_mode ty = By_reference ->
  expression_value ge environment temporaries memory (Evar identifier ty) (Vptr symbol Ptrofs.zero).
Proof. intros ABSENT SYMBOL REFERENCE; apply old_expression_value; eapply value_function; eassumption. Qed.

Lemma spawn_null_pointer_reference ge environment temporaries memory :
  expression_value ge environment temporaries memory (Ecast (Econst_int Int.zero tint) (tptr tvoid)) Vnullptr.
Proof. apply old_expression_value; eapply value_cast; [constructor |reflexivity]. Qed.

Theorem actual_spawn_vector_store ge environment temporaries blocks symbols index cell before after continuation :
  gateway_spawn_vector_locations ge environment blocks symbols ->
  nth_error (gateway_spawn_cell_plan blocks symbols) index = Some cell ->
  Mem.store (vector_cell_chunk cell) before (vector_cell_block cell) (vector_cell_offset cell)
    (vector_cell_value cell) = Some after ->
  store_edge ge (State f_host_exchange (spawn_vector_assignment index) continuation environment temporaries before)
    (State f_host_exchange Sskip continuation environment temporaries after).
Proof.
  intros LOCATIONS SELECTED STORE.
  destruct LOCATIONS as [CHILD ARGUMENTS ENVIRONMENT ENGINE_LOCAL PATH_LOCAL LOCALE_LOCAL ENGINE PATH LOCALE].
  assert (BOUND : (index < 6)%nat).
  { change (index < length (gateway_spawn_cell_plan blocks symbols))%nat.
    apply nth_error_Some; rewrite SELECTED; discriminate. }
  destruct index as [|[|[|[|[|[|index]]]]]]; try lia;
    cbn [gateway_spawn_cell_plan] in SELECTED; inversion SELECTED; subst cell.
  - eapply assignment_source_edge with (b := spawn_child_block blocks) (ofs := Ptrofs.zero)
      (v := Vint Int.zero) (w := Vint Int.zero).
    + apply local_location_value; exact CHILD.
    + apply old_expression_value; constructor.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity |exact STORE].
  - eapply spawn_array_store_edge with (object := spawn_arguments_block blocks) (index := 0)
      (value := Vptr (spawn_engine_symbol symbols) Ptrofs.zero).
    + exact ARGUMENTS.
    + lia.
    + eapply spawn_global_array_reference; [exact ENGINE_LOCAL |exact ENGINE |reflexivity].
    + reflexivity.
    + exact STORE.
  - eapply spawn_array_store_edge with (object := spawn_arguments_block blocks) (index := 1) (value := Vnullptr).
    + exact ARGUMENTS.
    + lia.
    + apply spawn_null_pointer_reference.
    + reflexivity.
    + exact STORE.
  - eapply spawn_array_store_edge with (object := spawn_environment_block blocks) (index := 0)
      (value := Vptr (spawn_path_symbol symbols) Ptrofs.zero).
    + exact ENVIRONMENT.
    + lia.
    + eapply spawn_global_array_reference; [exact PATH_LOCAL |exact PATH |reflexivity].
    + reflexivity.
    + exact STORE.
  - eapply spawn_array_store_edge with (object := spawn_environment_block blocks) (index := 1)
      (value := Vptr (spawn_locale_symbol symbols) Ptrofs.zero).
    + exact ENVIRONMENT.
    + lia.
    + eapply spawn_global_array_reference; [exact LOCALE_LOCAL |exact LOCALE |reflexivity].
    + reflexivity.
    + exact STORE.
  - eapply spawn_array_store_edge with (object := spawn_environment_block blocks) (index := 2) (value := Vnullptr).
    + exact ENVIRONMENT.
    + lia.
    + apply spawn_null_pointer_reference.
    + reflexivity.
    + exact STORE.
Qed.
