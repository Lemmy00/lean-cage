(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: Construct actual owned input cells at the generated symbols. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Slice Machine Readers Library LibraryWitnesses ProcessEffects Fault
  FreshMemoryDraft FailureSourceDraft FailureContractDraft.
Import ListNotations.
Open Scope Z_scope.

Lemma allocate_failure_string : forall base bytes,
  Forall (fun b => b <> Byte.zero) bytes -> (length bytes <= 158)%nat ->
  exists after b, old_memory base after /\ c_string after (global_address b) bytes /\
    b = Mem.nextblock base /\ Mem.nextblock after = Pos.succ (Mem.nextblock base).
Proof.
  intros base bytes NONZERO BOUND.
  destruct (allocated_bytes base (bytes++[Byte.zero])) as [allocated [b [after [ALLOC [STORE LOAD]]]]].
  assert (FRESH : ~ Mem.valid_block base b) by (eapply Mem.fresh_block_alloc; exact ALLOC).
  exists after, b; split.
  - eapply Mem.unchanged_on_trans; [eapply Mem.alloc_unchanged_on; exact ALLOC|].
    eapply Mem.storebytes_unchanged_on; [exact STORE|]. intros pos RANGE VALID; contradiction.
  - split.
    + split; [exact NONZERO|]. split.
      * unfold span_bounds, global_address; cbn [address_offset]. rewrite app_length; cbn [length].
        change (0 <= 0 < 18446744073709551616 /\
          0+Z.of_nat (length bytes+1) <= 18446744073709551616 /\
          Z.of_nat (length bytes+1) <= 18446744073709551615); lia.
      * exact LOAD.
    + split; [exact (Mem.alloc_result _ _ _ _ _ ALLOC)|].
      rewrite (Mem.nextblock_storebytes _ _ _ _ _ STORE), (Mem.nextblock_alloc _ _ _ _ _ ALLOC); reflexivity.
Qed.

Fixpoint empty_allocations n m := match n with
  | O => m | S rest => let '(after,_) := Mem.alloc m 0 0 in empty_allocations rest after end.
Lemma empty_allocations_preserve : forall n m, old_memory m (empty_allocations n m).
Proof.
  induction n; intros m; cbn; [apply Mem.unchanged_on_refl|].
  destruct (Mem.alloc m 0 0) as [after b] eqn:ALLOC.
  eapply Mem.unchanged_on_trans; [eapply Mem.alloc_unchanged_on; exact ALLOC|].
  eapply Mem.unchanged_on_implies; [exact (IHn after)|].
  intros block pos VALID VALIDAFTER; exact VALIDAFTER.
Qed.
Lemma empty_allocations_next : forall n m,
  Pos.to_nat (Mem.nextblock (empty_allocations n m)) = (Pos.to_nat (Mem.nextblock m) + n)%nat.
Proof.
  induction n; intros m; cbn; [lia|].
  destruct (Mem.alloc m 0 0) as [after b] eqn:ALLOC.
  rewrite IHn, (Mem.nextblock_alloc _ _ _ _ _ ALLOC), Pos2Nat.inj_succ; lia.
Qed.

Theorem failure_literal_symbols :
  Genv.find_symbol failure_ge ___stringlit_8 = Some 21%positive /\
  Genv.find_symbol failure_ge ___stringlit_9 = Some 23%positive /\
  Genv.find_symbol failure_ge _mode = Some 75%positive.
Proof. split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. Qed.

Theorem failure_inputs_inhabited : forall mode_bytes,
  Forall (fun b => b <> Byte.zero) mode_bytes -> (length mode_bytes <= 158)%nat ->
  exists cell m mode, failure_input cell m mode mode_bytes 21%positive 23%positive.
Proof.
  intros mode_bytes NONZERO LENGTH.
  destruct (allocate_failure_string (vacant_memory 21%positive) error_drop_bytes) as [m1 [drop [O1 [D1 [DROP N1]]]]].
  { repeat constructor; vm_compute; discriminate. }
  { cbn; lia. }
  change (drop=21%positive) in DROP; subst drop. change (Mem.nextblock m1=22%positive) in N1.
  destruct (allocate_failure_string m1 mode_bytes NONZERO LENGTH) as [m2 [mode [O2 [M2 [MODE N2]]]]].
  rewrite N1 in MODE, N2; change (Mem.nextblock m2=23%positive) in N2; subst mode.
  destruct (allocate_failure_string m2 error_short_bytes) as [m3 [short [O3 [S3 [SHORT N3]]]]].
  { repeat constructor; vm_compute; discriminate. }
  { cbn; lia. }
  rewrite N2 in SHORT, N3; change (Mem.nextblock m3=24%positive) in N3; subst short.
  set (gap := empty_allocations 51 m3).
  assert (OG : old_memory m3 gap) by apply empty_allocations_preserve.
  assert (NG : Mem.nextblock gap = 75%positive).
  { apply Pos2Nat.inj. unfold gap. rewrite empty_allocations_next, N3; reflexivity. }
  assert (DG : c_string gap (global_address 21%positive) error_drop_bytes).
  { eapply old_memory_string; [exact OG|]. eapply old_memory_string; [exact O3|]. eapply old_memory_string; eassumption. }
  assert (MG : c_string gap (global_address 22%positive) mode_bytes).
  { eapply old_memory_string; [exact OG|]. eapply old_memory_string; eassumption. }
  assert (SG : c_string gap (global_address 23%positive) error_short_bytes) by (eapply old_memory_string; eassumption).
  destruct (Mem.alloc gap 0 8) as [pointer_mem mb] eqn:ALLOC.
  assert (MB : mb=75%positive) by (rewrite (Mem.alloc_result _ _ _ _ _ ALLOC); exact NG); subst mb.
  assert (CELL : Mem.valid_access pointer_mem Mint64 75%positive 0 Writable).
  { eapply Mem.valid_access_implies with (p1:=Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact ALLOC|cbn; lia|cbn; lia|exists 0; reflexivity]. }
  destruct (Mem.valid_access_store _ _ _ _ (address_value (global_address 22%positive)) CELL) as [pointed STORE].
  assert (OP : old_memory gap pointed).
  { eapply Mem.unchanged_on_trans; [eapply Mem.alloc_unchanged_on; exact ALLOC|].
    eapply Mem.store_unchanged_on; [exact STORE|]. intros pos RANGE VALID.
    eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC); exact VALID. }
  destruct (Mem.alloc pointed 0 4) as [final eb] eqn:TLSALLOC.
  assert (OF : old_memory pointed final) by (eapply Mem.alloc_unchanged_on; exact TLSALLOC).
  exists {|tls_block:=eb;tls_offset:=0|}, final, (global_address 22%positive).
  destruct failure_literal_symbols as [DS [SS MS]].
  split.
  - unfold tls_ready; cbn. split; [lia|]. split; [change (4 <= 18446744073709551616); lia|].
    eapply Mem.valid_access_implies with (p1:=Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact TLSALLOC|cbn; lia|cbn; lia|exists 0; reflexivity].
  - split.
    + exists 75%positive; split; [exact MS|].
      change (Mem.load Mint64 final 75%positive 0 = Some (address_value (global_address 22%positive))).
      eapply old_memory_load; [exact OF|].
      exact (Mem.load_store_same _ _ _ _ _ _ STORE).
    + split.
      * eapply old_memory_string; [exact OF|]. eapply old_memory_string; eassumption.
      * split; [exact DS|]. split; [exact SS|]. split;
          (eapply old_memory_string; [exact OF|]); eapply old_memory_string; eassumption.
Qed.

Require Import LibraryMachine ReportingTraceDraft FailureMemoryDraft FailureTraceDraft FailureRunsDraft FailureErrorDraft.

Theorem failure_owned_complete_execution : forall mode_bytes fd stage error,
  Forall (fun b => b <> Byte.zero) mode_bytes -> (length mode_bytes <= 158)%nat ->
  exists cell base mode events final,
    failure_input cell base mode mode_bytes 21%positive 23%positive /\
    library_steps failure_ge cell (live (failure_initial fd stage error Kstop base))
      (events ++ [exit_requested (Int.repr 125)]) (dead final) /\
    reporting_trace events = selected_report mode_bytes stage error.
Proof.
  intros mode_bytes fd stage error NONZERO LENGTH.
  destruct (failure_inputs_inhabited mode_bytes NONZERO LENGTH) as [cell [base [mode INPUT]]].
  destruct (failure_successful_exit_exists cell base fd stage error mode mode_bytes 21%positive 23%positive Kstop INPUT I)
    as [events [final [RUN BYTES]]].
  exists cell, base, mode, events, final; auto.
Qed.

Theorem normal_failure_execution : forall fd stage error,
  exists cell base mode events final,
    failure_input cell base mode normal_bytes 21%positive 23%positive /\
    library_steps failure_ge cell (live (failure_initial fd stage error Kstop base))
      (events ++ [exit_requested (Int.repr 125)]) (dead final) /\
    reporting_trace events = failure_packet stage error.
Proof.
  intros fd stage error. apply (failure_owned_complete_execution normal_bytes fd stage error).
  - repeat constructor; vm_compute; discriminate.
  - cbn; lia.
Qed.

Theorem dropped_failure_execution : forall fd stage error,
  exists cell base mode events final,
    failure_input cell base mode error_drop_bytes 21%positive 23%positive /\
    library_steps failure_ge cell (live (failure_initial fd stage error Kstop base))
      (events ++ [exit_requested (Int.repr 125)]) (dead final) /\ reporting_trace events = [].
Proof.
  intros fd stage error. apply (failure_owned_complete_execution error_drop_bytes fd stage error).
  - repeat constructor; vm_compute; discriminate.
  - cbn; lia.
Qed.

Theorem short_failure_execution : forall fd stage error,
  exists cell base mode events final,
    failure_input cell base mode error_short_bytes 21%positive 23%positive /\
    library_steps failure_ge cell (live (failure_initial fd stage error Kstop base))
      (events ++ [exit_requested (Int.repr 125)]) (dead final) /\
    reporting_trace events = firstn 3 (failure_packet stage error).
Proof.
  intros fd stage error. apply (failure_owned_complete_execution error_short_bytes fd stage error).
  - repeat constructor; vm_compute; discriminate.
  - cbn; lia.
Qed.

Theorem failed_failure_execution : forall fd stage error write_error,
  write_error <> Int.repr 4 ->
  exists cell base mode events final request,
    failure_input cell base mode normal_bytes 21%positive 23%positive /\
    library_steps failure_ge cell (live (failure_initial fd stage error Kstop base))
      (events ++ [exit_requested (Int.repr 125)]) (dead final) /\
    In (original_event (io_step request (IO.failure write_error))) events.
Proof.
  intros fd stage error write_error ERROR.
  destruct (failure_inputs_inhabited normal_bytes) as [cell [base [mode INPUT]]].
  - repeat constructor; vm_compute; discriminate.
  - cbn; lia.
  - destruct (failure_failed_report_exit_exists cell base fd stage error mode normal_bytes 21%positive 23%positive Kstop write_error INPUT I eq_refl ERROR)
      as [events [final [request [RUN ERRORIN]]]].
    exists cell, base, mode, events, final, request; auto.
Qed.

Theorem lost_failure_execution : forall waits fd stage error,
  exists cell base mode events final,
    failure_input cell base mode normal_bytes 21%positive 23%positive /\
    library_steps failure_ge cell (live (failure_initial fd stage error Kstop base)) events (dead final) /\
    reporting_trace events = firstn 1 (failure_packet stage error) /\
    exists before request, events = before ++ map original_event
      (repeat wait_step waits ++ [partial_loss request (firstn 1 (failure_packet stage error)) None]).
Proof.
  intros waits fd stage error.
  destruct (failure_inputs_inhabited normal_bytes) as [cell [base [mode INPUT]]].
  - repeat constructor; vm_compute; discriminate.
  - cbn; lia.
  - destruct (failure_partial_loss_exists waits cell base fd stage error mode normal_bytes 21%positive 23%positive Kstop
      (firstn 1 (failure_packet stage error)) (skipn 1 (failure_packet stage error)) INPUT I eq_refl)
      as [events [final [RUN FACTS]]].
    + rewrite firstn_skipn; reflexivity.
    + discriminate.
    + exists cell, base, mode, events, final; auto.
Qed.
