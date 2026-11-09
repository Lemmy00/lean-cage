(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.clock: The actual machine preserves the pre-existing TLS allocation identity. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Cop Clight.
Require Import IO Machine Library LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
Import ListNotations.
Local Open Scope Z_scope.

Definition machine_memory state := match state with live source=>memory_of source|dead memory=>memory end.

Lemma source_storev_valid chunk before address value after object :
  Mem.storev chunk before address value=Some after ->
  Mem.valid_block before object -> Mem.valid_block after object.
Proof.
  unfold Mem.storev;destruct address;try discriminate.
  destruct (zle _ _);try discriminate.
  intros STORE VALID;eapply Mem.store_valid_block_1;eassumption.
Qed.

Lemma source_assign_valid ge ty before block offset field value after object :
  assign_loc ge ty before block offset field value after ->
  Mem.valid_block before object -> Mem.valid_block after object.
Proof.
  intros ASSIGN VALID;inversion ASSIGN;subst.
  - eapply source_storev_valid;eassumption.
  - eapply Mem.storebytes_valid_block_1;eassumption.
  - match goal with BITFIELD:store_bitfield _ _ _ _ _ _ _ _ _ _|-_=>inversion BITFIELD;subst end.
    eapply source_storev_valid;eassumption.
Qed.

Lemma source_alloc_variables_valid ge env before vars result after object :
  alloc_variables ge env before vars result after ->
  Mem.valid_block before object -> Mem.valid_block after object.
Proof.
  intro ALLOC;induction ALLOC;intro VALID;[exact VALID|].
  apply IHALLOC;eapply Mem.valid_block_alloc;eassumption.
Qed.

Lemma source_free_list_valid blocks before after object :
  Mem.free_list before blocks=Some after ->
  Mem.valid_block before object -> Mem.valid_block after object.
Proof.
  revert before;induction blocks as [|[[block low] high] rest IH];intros before FREE VALID;
    cbn[Mem.free_list] in FREE.
  - inversion FREE;subst;exact VALID.
  - destruct (Mem.free before block low high) as [middle|] eqn:RELEASE;try discriminate.
    eapply IH;[exact FREE|];eapply Mem.valid_block_free_1;eassumption.
Qed.

Lemma internal_source_valid ge before trace after object :
  internal_state before ->step2 ge before trace after ->
  Mem.valid_block (memory_of before) object ->Mem.valid_block (memory_of after) object.
Proof.
  intros INTERNAL STEP VALID;inversion STEP;subst;cbn in *;try contradiction;try exact VALID.
  - eapply source_assign_valid;eassumption.
  - eapply source_free_list_valid;eassumption.
  - eapply source_free_list_valid;eassumption.
  - eapply source_free_list_valid;eassumption.
  - match goal with ENTRY:function_entry2 _ _ _ _ _ _ _|-_=>inversion ENTRY;subst end.
    eapply source_alloc_variables_valid;eassumption.
Qed.

Lemma errno_change_valid request before error after object :
  errno_change request before error after ->Mem.valid_block before object ->Mem.valid_block after object.
Proof.
  intros CHANGE VALID;inversion CHANGE;subst;[exact VALID|].
  eapply Mem.store_valid_block_1;eassumption.
Qed.

Lemma io_return_valid request before reply after object :
  io_return request before reply after ->Mem.valid_block before object ->Mem.valid_block after object.
Proof.
  intros RETURN VALID;inversion RETURN;subst;
    try solve[eapply errno_change_valid;eassumption].
  eapply errno_change_valid;[eassumption|].
  eapply Mem.storebytes_valid_block_1;eassumption.
Qed.

Lemma machine_step_valid ge cell before event after object :
  Machine.step ge cell before event after ->
  Mem.valid_block (machine_memory before) object ->Mem.valid_block (machine_memory after) object.
Proof.
  intros STEP VALID;inversion STEP;subst;cbn[machine_memory] in *;try exact VALID.
  - eapply internal_source_valid;eassumption.
  - eapply io_return_valid;eassumption.
  - eapply io_return_valid;eassumption.
Qed.

Lemma library_step_valid ge cell before event after object :
  library_step ge cell before event after ->
  Mem.valid_block (machine_memory before) object ->Mem.valid_block (machine_memory after) object.
Proof.
  intros STEP VALID;inversion STEP;subst;cbn[machine_memory] in *;try exact VALID.
  - eapply machine_step_valid;eassumption.
  - match goal with COPY:copy_result _ _ _ _ _|-_=>destruct COPY as [_ STORE] end.
    eapply Mem.storebytes_valid_block_1;eassumption.
  - eapply Mem.valid_block_unchanged_on;[eapply partial_copy_outside;eassumption|exact VALID].
  - eapply Mem.valid_block_unchanged_on;[eapply close_preserves_outside_tls;eassumption|exact VALID].
Qed.

Lemma entry_step_valid ge cell before event after object :
  entry_handoff_step ge cell before event after ->
  Mem.valid_block (machine_memory before) object ->Mem.valid_block (machine_memory after) object.
Proof.
  intros STEP VALID;inversion STEP;subst;cbn[machine_memory] in *;try exact VALID.
  - eapply library_step_valid;eassumption.
  - eapply Mem.valid_block_unchanged_on;[eapply entry_format_frame;eassumption|exact VALID].
  - eapply Mem.valid_block_unchanged_on;[eapply entry_format_partial_frame;eassumption|exact VALID].
  - eapply Mem.valid_block_unchanged_on;eassumption.
  - eapply Mem.valid_block_unchanged_on;[eapply entry_errno_partial_frame;eassumption|exact VALID].
  - eapply Mem.valid_block_unchanged_on;eassumption.
  - eapply Mem.valid_block_unchanged_on;[eapply entry_errno_partial_frame;eassumption|exact VALID].
Qed.

Lemma errno_ready_valid cell memory : entry_errno_ready cell memory ->
  Mem.valid_block memory (tls_block cell).
Proof.
  intros [error [LOW [HIGH [ACCESS LOAD]]]].
  eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.

Theorem process_step_tls_valid ge cell before event after :
  process_step ge cell before event after ->
  Mem.valid_block (machine_memory before) (tls_block cell) ->
  Mem.valid_block (machine_memory after) (tls_block cell).
Proof.
  intros STEP VALID;inversion STEP;subst;cbn[machine_memory] in *;try exact VALID;
    try solve[eapply errno_ready_valid;eassumption].
  - eapply entry_step_valid;eassumption.
  - match goal with PARTIAL:process_wait_partial _ _ _ _ _|-_=>destruct PARTIAL as [FRAME _] end.
    eapply Mem.valid_block_unchanged_on;eassumption.
  - match goal with PARTIAL:process_ptrace_partial _ _ _ _ _|-_=>destruct PARTIAL as [FRAME _] end.
    unfold process_ptrace_frame in FRAME;destruct (Int.eq request (Int.repr 16898));
      [destruct data|];eapply Mem.valid_block_unchanged_on;eassumption.
  - match goal with PARTIAL:process_clock_partial _ _ _ _ _|-_=>destruct PARTIAL as [FRAME _] end.
    eapply Mem.valid_block_unchanged_on;eassumption.
  - eapply Mem.valid_block_unchanged_on;[eapply entry_errno_partial_frame;eassumption|exact VALID].
  - eapply Mem.valid_block_unchanged_on;[eapply entry_errno_partial_frame;eassumption|exact VALID].
Qed.

Theorem process_steps_tls_valid ge cell before events after :
  process_steps ge cell before events after ->
  Mem.valid_block (machine_memory before) (tls_block cell) ->
  Mem.valid_block (machine_memory after) (tls_block cell).
Proof.
  intro RUN;induction RUN;intro VALID;[exact VALID|].
  apply IHRUN;eapply process_step_tls_valid;eassumption.
Qed.
