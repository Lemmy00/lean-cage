(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Each native vector store retains earlier actual initialized cells. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Memory Memdata.
Import ListNotations.
Open Scope Z_scope.

Record gateway_vector_cell := {
  vector_cell_block : block;
  vector_cell_offset : Z;
  vector_cell_chunk : memory_chunk;
  vector_cell_value : val
}.

Definition gateway_vector_writable memory cell :=
  Mem.valid_access memory (vector_cell_chunk cell) (vector_cell_block cell) (vector_cell_offset cell) Writable.
Definition gateway_vector_loaded memory cell :=
  Mem.load (vector_cell_chunk cell) memory (vector_cell_block cell) (vector_cell_offset cell) =
    Some (vector_cell_value cell).
Definition gateway_vector_typed cell :=
  Val.load_result (vector_cell_chunk cell) (vector_cell_value cell) = vector_cell_value cell.
Definition gateway_vector_separate first second :=
  vector_cell_block first <> vector_cell_block second \/
  vector_cell_offset first + size_chunk (vector_cell_chunk first) <= vector_cell_offset second \/
  vector_cell_offset second + size_chunk (vector_cell_chunk second) <= vector_cell_offset first.
Definition gateway_vector_span (cells : list gateway_vector_cell) object position : Prop :=
  exists cell, In cell cells /\ vector_cell_block cell = object /\
    vector_cell_offset cell <= position < vector_cell_offset cell + size_chunk (vector_cell_chunk cell).

Lemma gateway_vector_store_access before after target cells :
  Mem.store (vector_cell_chunk target) before (vector_cell_block target) (vector_cell_offset target)
    (vector_cell_value target) = Some after ->
  Forall (gateway_vector_writable before) cells -> Forall (gateway_vector_writable after) cells.
Proof.
  intros STORE; apply Forall_impl; intros cell ACCESS.
  eapply Mem.store_valid_access_1; eassumption.
Qed.

Lemma gateway_vector_store_preserves_loaded before after target initialized :
  Mem.store (vector_cell_chunk target) before (vector_cell_block target) (vector_cell_offset target)
    (vector_cell_value target) = Some after ->
  gateway_vector_typed target ->
  Forall (fun cell => gateway_vector_separate cell target) initialized ->
  Forall (gateway_vector_loaded before) initialized ->
  Forall (gateway_vector_loaded after) (initialized ++ [target]).
Proof.
  intros STORE TYPED SEPARATE LOADED; apply Forall_app; split.
  - rewrite Forall_forall in *; intros cell MEMBER.
    specialize (SEPARATE cell MEMBER); specialize (LOADED cell MEMBER).
    unfold gateway_vector_loaded in *.
    erewrite Mem.load_store_other; [exact LOADED | exact STORE | exact SEPARATE].
  - constructor; [|constructor].
    unfold gateway_vector_loaded; rewrite (Mem.load_store_same _ _ _ _ _ _ STORE), TYPED; reflexivity.
Qed.

Theorem gateway_vector_store before target cells initialized :
  gateway_vector_writable before target -> gateway_vector_typed target ->
  Forall (gateway_vector_writable before) cells ->
  Forall (fun cell => gateway_vector_separate cell target) initialized ->
  Forall (gateway_vector_loaded before) initialized ->
  exists after,
    Mem.store (vector_cell_chunk target) before (vector_cell_block target) (vector_cell_offset target)
      (vector_cell_value target) = Some after /\
    Forall (gateway_vector_writable after) cells /\
    Forall (gateway_vector_loaded after) (initialized ++ [target]).
Proof.
  intros WRITABLE TYPED ACCESS SEPARATE LOADED.
  destruct (Mem.valid_access_store _ _ _ _ (vector_cell_value target) WRITABLE) as [after STORE].
  exists after; split; [exact STORE |]. split.
  - eapply gateway_vector_store_access; eassumption.
  - eapply gateway_vector_store_preserves_loaded; eassumption.
Qed.

Lemma gateway_vector_access_frame before after cells :
  Mem.unchanged_on (gateway_vector_span cells) before after ->
  Forall (gateway_vector_writable before) cells -> Forall (gateway_vector_writable after) cells.
Proof.
  intros FRAME ACCESS; rewrite Forall_forall in *; intros cell MEMBER.
  destruct (ACCESS cell MEMBER) as [RANGE ALIGN]; split; [|exact ALIGN].
  intros position INSIDE; eapply Mem.perm_unchanged_on; [exact FRAME | |apply RANGE; exact INSIDE].
  exists cell; split; [exact MEMBER |]. split; [reflexivity |exact INSIDE].
Qed.

Lemma gateway_vector_loaded_frame before after cells :
  Mem.unchanged_on (gateway_vector_span cells) before after ->
  Forall (gateway_vector_loaded before) cells -> Forall (gateway_vector_loaded after) cells.
Proof.
  intros FRAME LOADED; rewrite Forall_forall in *; intros cell MEMBER.
  eapply Mem.load_unchanged_on; [exact FRAME | |apply LOADED; exact MEMBER].
  intros position INSIDE; exists cell; split; [exact MEMBER |]. split; [reflexivity |exact INSIDE].
Qed.
