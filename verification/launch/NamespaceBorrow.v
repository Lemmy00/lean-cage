(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Preserve shared guest input borrows through actual local primitive effects. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Machine Library ProcessEffects FreshMemory ReceiverAllocation.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceAllocation.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Definition namespace_borrow_frame := handoff_borrowed_frame.

Theorem namespace_errno_effect_preserves_borrows cell before after input :
  handoff_borrowed_input cell before input -> entry_errno_partial cell before after ->
  entry_errno_ready cell after -> handoff_borrowed_input cell after input.
Proof.
  intros INPUT FRAME ERRNO; eapply handoff_borrowed_input_framed; [exact INPUT| |exact ERRNO].
  eapply Mem.unchanged_on_implies; [exact (entry_errno_partial_frame _ _ _ FRAME)|].
  intros object offset MEMBER VALID; left.
  pose proof (handoff_borrowed_tls_separate _ _ _ INPUT) as TLS.
  rewrite Forall_forall in TLS; apply TLS; exact MEMBER.
Qed.

Theorem namespace_store_preserves_borrows cell input before object offset chunk value after :
  handoff_borrowed_input cell before input -> ~In object (handoff_borrowed_blocks input) ->
  object <> tls_block cell -> Mem.store chunk before object offset value = Some after ->
  handoff_borrowed_input cell after input.
Proof.
  intros INPUT PRIVATE TLS STORE; eapply handoff_borrowed_input_framed; [exact INPUT| |].
  - eapply Mem.store_unchanged_on; [exact STORE|].
    intros position RANGE MEMBER; apply PRIVATE; exact MEMBER.
  - destruct (handoff_borrowed_errno _ _ _ INPUT) as [error [LOW [HIGH [ACCESS LOAD]]]].
    exists error; split; [exact LOW|]. split; [exact HIGH|]. split.
    + destruct ACCESS as [PERMISSIONS ALIGN]; split; [|exact ALIGN].
      intros position RANGE; eapply Mem.perm_store_1; [exact STORE|apply PERMISSIONS; exact RANGE].
    + rewrite (Mem.load_store_other _ _ _ _ _ _ STORE) by (left; congruence); exact LOAD.
Qed.

Theorem namespace_pair_preserves_borrows cell before after input object offset returned first second :
  handoff_borrowed_input cell before input -> ~In object (handoff_borrowed_blocks input) ->
  object <> tls_block cell -> namespace_pair_effect cell object offset before returned first second after ->
  entry_errno_ready cell after -> handoff_borrowed_input cell after input.
Proof.
  intros INPUT PRIVATE TLS PAIR ERRNO; inversion PAIR; subst.
  - eapply namespace_errno_effect_preserves_borrows; eassumption.
  - eapply namespace_errno_effect_preserves_borrows; [|eassumption|exact ERRNO].
    eapply namespace_store_preserves_borrows; [|exact PRIVATE|exact TLS|eassumption].
    eapply namespace_store_preserves_borrows; eassumption.
Qed.

Theorem namespace_close_preserves_borrows cell before after input reply :
  handoff_borrowed_input cell before input -> close_effect cell before reply after ->
  entry_errno_ready cell after -> handoff_borrowed_input cell after input.
Proof.
  intros INPUT CLOSE ERRNO; eapply handoff_borrowed_input_framed; [exact INPUT| |exact ERRNO].
  eapply Mem.unchanged_on_implies; [eapply close_preserves_outside_tls; exact CLOSE|].
  intros object offset MEMBER VALID; left.
  pose proof (handoff_borrowed_tls_separate _ _ _ INPUT) as TLS.
  rewrite Forall_forall in TLS; apply TLS; exact MEMBER.
Qed.

Theorem namespace_fresh_local_separate_borrows cell input before object :
  handoff_borrowed_input cell before input -> ~Mem.valid_block before object ->
  ~In object (handoff_borrowed_blocks input).
Proof.
  intros INPUT FRESH MEMBER; apply FRESH.
  pose proof (handoff_borrowed_objects_valid _ _ _ INPUT) as VALID.
  rewrite Forall_forall in VALID; apply VALID; exact MEMBER.
Qed.

Theorem namespace_allocation_preserves_borrows cell input before objects after :
  handoff_borrowed_input cell before input -> local_allocations before objects after ->
  handoff_borrowed_input cell after input.
Proof.
  intros INPUT ALLOC; eapply handoff_borrowed_input_framed; [exact INPUT| |].
  - eapply Mem.unchanged_on_implies; [eapply local_allocations_unchanged; exact ALLOC|].
    intros object offset MEMBER VALID.
    pose proof (handoff_borrowed_objects_valid _ _ _ INPUT) as BLOCKS.
    rewrite Forall_forall in BLOCKS; apply BLOCKS; exact MEMBER.
  - destruct (handoff_borrowed_errno _ _ _ INPUT) as [error OWN]; exists error.
    destruct OWN as [LOW [HIGH [ACCESS LOAD]]].
    split; [exact LOW|]. split; [exact HIGH|]. split.
    + destruct ACCESS as [PERMISSIONS ALIGN]; split; [|exact ALIGN].
      intros position RANGE; eapply local_allocations_perms; [exact ALLOC|apply PERMISSIONS; exact RANGE].
    + eapply old_memory_load; [eapply local_allocations_unchanged; exact ALLOC|exact LOAD].
Qed.

Theorem namespace_free_preserves_borrows cell input before after object low high :
  handoff_borrowed_input cell before input -> ~In object (handoff_borrowed_blocks input) ->
  object <> tls_block cell -> Mem.free before object low high = Some after ->
  handoff_borrowed_input cell after input.
Proof.
  intros INPUT PRIVATE TLS FREE; eapply handoff_borrowed_input_framed; [exact INPUT| |].
  - eapply Mem.free_unchanged_on; [exact FREE|].
    intros position RANGE MEMBER; apply PRIVATE; exact MEMBER.
  - destruct (handoff_borrowed_errno _ _ _ INPUT) as [error [LOW [HIGH [ACCESS LOAD]]]].
    exists error; split; [exact LOW|]. split; [exact HIGH|]. split.
    + destruct ACCESS as [PERMISSIONS ALIGN]; split; [|exact ALIGN].
      intros position RANGE; eapply Mem.perm_free_1; [exact FREE|left; congruence|].
      apply PERMISSIONS; exact RANGE.
    + eapply Mem.load_unchanged_on with (P:=fun target _=>target<>object);
        [eapply Mem.free_unchanged_on; [exact FREE|]| |exact LOAD].
      * intros position RANGE DIFFERENT; apply DIFFERENT; reflexivity.
      * intros position RANGE; congruence.
Qed.
