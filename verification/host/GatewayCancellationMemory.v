(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Marking cancellation changes its actual owned field only. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayStreamInterface GatewayStreamMemory GatewayReadMemory
  GatewayReadContext GatewayThreadRuntime GatewayReadyInterface.
Open Scope Z_scope.

Definition gateway_stream_mark_cancelled initial : gateway_stream_values := {|
  stream_descriptor := stream_descriptor initial;
  stream_control := stream_control initial;
  stream_cancel_sent := Int.one;
  stream_cli := stream_cli initial;
  stream_cancellation := stream_cancellation initial;
  stream_remaining := stream_remaining initial;
  stream_nodes := stream_nodes initial;
  stream_deadline := stream_deadline initial
|}.

Lemma gateway_stream_mark_transport initial :
  gateway_stream_transport_after initial (gateway_stream_mark_cancelled initial).
Proof. unfold gateway_stream_transport_after; cbn; tauto. Qed.

Lemma gateway_stream_transport_reflexive initial : gateway_stream_transport_after initial initial.
Proof. unfold gateway_stream_transport_after; tauto. Qed.

Lemma gateway_stream_transport_transitive first second third :
  gateway_stream_transport_after first second -> gateway_stream_transport_after second third ->
  gateway_stream_transport_after first third.
Proof.
  unfold gateway_stream_transport_after.
  intros (D1 & C1 & L1 & P1 & R1 & N1 & T1 & S1)
    (D2 & C2 & L2 & P2 & R2 & N2 & T2 & S2).
  repeat split; try congruence.
  destruct S2 as [SAME | MARKED]; [rewrite SAME; exact S1 | right; exact MARKED].
Qed.

Lemma gateway_cancel_store_exists before stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
  exists after, Mem.store Mint32 before stream_block (Ptrofs.unsigned stream_offset + 8)
    (Vint Int.one) = Some after.
Proof.
  intro INPUT.
  pose proof (proj1 (proj2 (proj2 (gateway_read_stream_cells _ _ _ _ _ _ _ _ INPUT)))) as LOAD.
  unfold Mem.loadv, gateway_stream_slot in LOAD.
  rewrite (gateway_stream_slot_unsigned stream_offset 8) in LOAD
    by (try exact (gateway_read_stream_bounds _ _ _ _ _ _ _ _ INPUT); lia).
  destruct (zle (Ptrofs.unsigned stream_offset + 8 + size_chunk Mint32) Ptrofs.modulus);
    [|discriminate].
  pose proof (Mem.load_valid_access _ _ _ _ _ LOAD) as [READABLE ALIGNED].
  assert (ACCESS : Mem.valid_access before Mint32 stream_block
    (Ptrofs.unsigned stream_offset + 8) Writable).
  { split; [|exact ALIGNED].
    intros position RANGE; apply (gateway_read_stream_owned _ _ _ _ _ _ _ _ INPUT position).
    cbn [size_chunk] in RANGE; lia. }
  destruct (Mem.valid_access_store before Mint32 stream_block (Ptrofs.unsigned stream_offset + 8)
    (Vint Int.one) ACCESS) as [after STORE]; exists after; exact STORE.
Qed.

Lemma gateway_stream_cell_cancel_store_other before after block offset chunk delta value :
  Ptrofs.unsigned offset + 48 <= Ptrofs.modulus ->
  0 <= delta -> delta + size_chunk chunk <= 48 ->
  (delta + size_chunk chunk <= 8 \/ 12 <= delta) ->
  Mem.store Mint32 before block (Ptrofs.unsigned offset + 8) (Vint Int.one) = Some after ->
  Mem.loadv chunk before (gateway_stream_slot block offset delta) = Some value ->
  Mem.loadv chunk after (gateway_stream_slot block offset delta) = Some value.
Proof.
  intros BOUND DELTA WIDTH SEPARATE STORE LOAD.
  unfold Mem.loadv, gateway_stream_slot in *.
  rewrite (gateway_stream_slot_unsigned offset delta) in LOAD |- * by
    (try exact BOUND; pose proof (size_chunk_pos chunk); lia).
  destruct (zle (Ptrofs.unsigned offset + delta + size_chunk chunk) Ptrofs.modulus); [|lia].
  erewrite Mem.load_store_other; [exact LOAD | exact STORE |].
  right; destruct SEPARATE; [left | right]; cbn [size_chunk]; lia.
Qed.

Lemma gateway_stream_mark_cells before after block offset initial :
  Ptrofs.unsigned offset + 48 <= Ptrofs.modulus ->
  gateway_stream_memory before block offset initial ->
  Mem.store Mint32 before block (Ptrofs.unsigned offset + 8) (Vint Int.one) = Some after ->
  gateway_stream_memory after block offset (gateway_stream_mark_cancelled initial).
Proof.
  intros BOUND [DESCRIPTOR [CONTROL [CANCEL [CLI [CANCELLATION [REMAINING [NODES DEADLINE]]]]]]] STORE.
  unfold gateway_stream_memory; cbn [gateway_stream_mark_cancelled].
  assert (CANCELLED : Mem.loadv Mint32 after (gateway_stream_slot block offset 8) = Some (Vint Int.one)).
  { unfold Mem.loadv, gateway_stream_slot.
    rewrite (gateway_stream_slot_unsigned offset 8) by (try exact BOUND; lia).
    destruct (zle (Ptrofs.unsigned offset + 8 + size_chunk Mint32) Ptrofs.modulus); [|cbn in *; lia].
    erewrite Mem.load_store_same by exact STORE; reflexivity. }
  repeat split; try exact CANCELLED;
    eapply gateway_stream_cell_cancel_store_other; try exact BOUND; try exact STORE;
    try exact DESCRIPTOR; try exact CONTROL; try exact CLI; try exact CANCELLATION;
    try exact REMAINING; try exact NODES; try exact DEADLINE; cbn [size_chunk]; try lia.
  change (16 + 8 <= 48); lia.
Qed.

Lemma gateway_mark_cancel_read_inputs before after stream_block stream_offset initial
    data_block data_offset amount readonly :
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
  Mem.store Mint32 before stream_block (Ptrofs.unsigned stream_offset + 8) (Vint Int.one) = Some after ->
  gateway_read_inputs after stream_block stream_offset (gateway_stream_mark_cancelled initial)
    data_block data_offset amount readonly /\
  Mem.unchanged_on (fun block position => readonly block position \/
    gateway_data_region data_block data_offset amount block position) before after /\
  (forall block position kind permission,
    Mem.perm before block position kind permission <-> Mem.perm after block position kind permission).
Proof.
  intros INPUT STORE.
  assert (PERMISSIONS : forall block position kind permission,
    Mem.perm before block position kind permission <-> Mem.perm after block position kind permission).
  { intros; split; [eapply Mem.perm_store_1 | eapply Mem.perm_store_2]; exact STORE. }
  assert (FRAME : Mem.unchanged_on (fun block position => readonly block position \/
    gateway_data_region data_block data_offset amount block position) before after).
  { eapply Mem.store_unchanged_on; [exact STORE |].
    intros position RANGE [READONLY | [SAME DATA]]; cbn [size_chunk] in RANGE.
    - exact (gateway_read_readonly_cancel _ _ _ _ _ _ _ _ INPUT position ltac:(lia) READONLY).
    - subst data_block; destruct (gateway_read_data_separate _ _ _ _ _ _ _ _ INPUT)
        as [DIFFERENT | [BEFORE | AFTER]]; [congruence | lia | lia]. }
  split; [|split; assumption].
  destruct INPUT as [CELLS AMOUNT STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
  constructor.
  - eapply gateway_stream_mark_cells; eassumption.
  - exact AMOUNT.
  - exact STREAM_BOUND.
  - exact DATA_BOUND.
  - intros position RANGE; apply (proj1 (PERMISSIONS _ _ _ _)); apply STREAM_PERM; exact RANGE.
  - eapply Mem.store_valid_block_1; eassumption.
  - intros position RANGE; apply (proj1 (PERMISSIONS _ _ _ _)); apply DATA_PERM; exact RANGE.
  - exact SEPARATE.
  - intros block position HERE; eapply Mem.store_valid_block_1; [exact STORE | apply READONLY_LIVE with (position := position); exact HERE].
  - intros block position HERE; apply (proj1 (PERMISSIONS _ _ _ _)); apply READONLY_READABLE; exact HERE.
  - exact READONLY_DATA.
  - exact READONLY_REMAINING.
  - exact READONLY_CANCEL.
Qed.
