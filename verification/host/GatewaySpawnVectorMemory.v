(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual launch slots are writable and disjoint before their ordered stores. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayVectorCells.
Import ListNotations.
Open Scope Z_scope.

Record gateway_spawn_vector_blocks := {
  spawn_child_block : block;
  spawn_arguments_block : block;
  spawn_environment_block : block
}.
Record gateway_spawn_vector_symbols := {
  spawn_engine_symbol : block;
  spawn_path_symbol : block;
  spawn_locale_symbol : block
}.

Definition spawn_pointer_cell object offset value :=
  {| vector_cell_block := object; vector_cell_offset := offset; vector_cell_chunk := Mptr; vector_cell_value := value |}.
Definition gateway_spawn_cell_plan blocks symbols :=
  [{| vector_cell_block := spawn_child_block blocks; vector_cell_offset := 0;
      vector_cell_chunk := Mint32; vector_cell_value := Vint Int.zero |};
   spawn_pointer_cell (spawn_arguments_block blocks) 0 (Vptr (spawn_engine_symbol symbols) Ptrofs.zero);
   spawn_pointer_cell (spawn_arguments_block blocks) 8 Vnullptr;
   spawn_pointer_cell (spawn_environment_block blocks) 0 (Vptr (spawn_path_symbol symbols) Ptrofs.zero);
   spawn_pointer_cell (spawn_environment_block blocks) 8 (Vptr (spawn_locale_symbol symbols) Ptrofs.zero);
   spawn_pointer_cell (spawn_environment_block blocks) 16 Vnullptr].

Definition gateway_spawn_blocks_distinct blocks :=
  spawn_child_block blocks <> spawn_arguments_block blocks /\
  spawn_child_block blocks <> spawn_environment_block blocks /\
  spawn_arguments_block blocks <> spawn_environment_block blocks.

Lemma gateway_spawn_vector_typed blocks symbols :
  Forall gateway_vector_typed (gateway_spawn_cell_plan blocks symbols).
Proof. repeat constructor. Qed.

Lemma gateway_spawn_vector_before_separate blocks symbols index selected :
  gateway_spawn_blocks_distinct blocks ->
  nth_error (gateway_spawn_cell_plan blocks symbols) index = Some selected ->
  Forall (fun cell => gateway_vector_separate cell selected)
    (firstn index (gateway_spawn_cell_plan blocks symbols)).
Proof.
  intros [CHILD_ARGUMENTS [CHILD_ENVIRONMENT ARGUMENTS_ENVIRONMENT]] SELECTED.
  assert (BOUND : (index < 6)%nat).
  { change (index < length (gateway_spawn_cell_plan blocks symbols))%nat.
    apply nth_error_Some; rewrite SELECTED; discriminate. }
  destruct index as [|[|[|[|[|[|index]]]]]]; cbn in SELECTED; try discriminate;
    try lia; inversion SELECTED; subst; cbn [firstn gateway_spawn_cell_plan];
    apply Forall_forall; intros cell MEMBER; cbn in MEMBER;
    repeat destruct MEMBER as [SAME | MEMBER]; try contradiction; subst cell;
    unfold gateway_vector_separate, spawn_pointer_cell; change Mptr with Mint64 in *;
    cbn; intuition lia.
Qed.

Lemma gateway_native_range_access memory object width chunk offset :
  Mem.range_perm memory object 0 width Cur Freeable ->
  0 <= offset -> offset + size_chunk chunk <= width ->
  (align_chunk chunk | offset) -> Mem.valid_access memory chunk object offset Writable.
Proof.
  intros RANGE LOW HIGH ALIGN; split; [|exact ALIGN].
  intros position INSIDE; eapply Mem.perm_implies; [apply RANGE; lia |constructor].
Qed.

Theorem gateway_spawn_vectors_writable memory blocks symbols :
  Mem.range_perm memory (spawn_child_block blocks) 0 4 Cur Freeable ->
  Mem.range_perm memory (spawn_arguments_block blocks) 0 16 Cur Freeable ->
  Mem.range_perm memory (spawn_environment_block blocks) 0 24 Cur Freeable ->
  Forall (gateway_vector_writable memory) (gateway_spawn_cell_plan blocks symbols).
Proof.
  intros CHILD ARGUMENTS ENVIRONMENT.
  apply Forall_forall; intros cell MEMBER; cbn [gateway_spawn_cell_plan] in MEMBER;
    repeat destruct MEMBER as [SAME | MEMBER]; try contradiction; subst cell;
    unfold gateway_vector_writable, spawn_pointer_cell; change Mptr with Mint64 in *; cbn;
    eapply gateway_native_range_access; try eassumption; try lia;
    cbn; try lia; first [exists 0; reflexivity |exists 1; reflexivity |exists 2; reflexivity].
Qed.

Lemma gateway_spawn_pointer_cells memory object first second :
  gateway_vector_loaded memory (spawn_pointer_cell object 0 first) ->
  gateway_vector_loaded memory (spawn_pointer_cell object 8 second) ->
  second = Vnullptr ->
  Mem.loadv Mptr memory (Vptr object Ptrofs.zero) = Some first /\
  Mem.loadv Mptr memory (Vptr object (Ptrofs.add Ptrofs.zero (Ptrofs.repr 8))) = Some Vnullptr.
Proof. intros FIRST SECOND NULL; subst second; split; assumption. Qed.
