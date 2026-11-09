(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The production failure routine cannot return into guest setup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteMemory WriteAll WriteBytes Writers
  StoreSteps LocalAccess CallAccess Library LibraryMachine LibraryPreservation LibraryControl
  ProcessEffects CallContexts CallPaths CallProgressDraft HelperProgressDraft WriteCallers FreshMemoryDraft.
From EntryNative Require Import EntrySource.
From EntryFailure Require Import FailureSource FailureMemory FailureBranches.
Import ListNotations.
Open Scope Z_scope.

Theorem current_failure_body_exact : EntrySource.f_fail_child = Slice.f_fail_child.
Proof. reflexivity. Qed.
Theorem current_failure_write_exact : EntrySource.f_write_all = Slice.f_write_all.
Proof. reflexivity. Qed.
Theorem current_failure_put_exact : EntrySource.f_put32 = Slice.f_put32.
Proof. reflexivity. Qed.

Lemma current_write_symbols : WriteAll.symbols failure_ge.
Proof.
  split; eexists; split; vm_compute; reflexivity.
Qed.

(* This uses the generic accepted invariant, not its old closed-ge corollary. *)
Theorem current_write_progress q input m :
  write_owned q input m ->
  procedure_progress failure_ge (cell_of q) (WriteAll.initial_state q m)
    (fun value after => write_owned q input after /\
      (value = Vint Int.zero \/ value = Vint Int.mone)).
Proof.
  intros OWN events s RUN.
  pose proof (WriteAll.invariant_initial failure_ge q input m current_write_symbols OWN) as INITIAL.
  destruct (write_all_library_invariant_projection _ _ _ _ _ _ RUN current_write_symbols _ _ INITIAL)
    as [original [EVENTS ORIGINAL]].
  pose proof (write_all_invariant_runs _ _ _ _ _ _ ORIGINAL current_write_symbols _ _ INITIAL) as INV.
  destruct (write_all_invariant_progress _ _ _ _ _ _ INV)
    as [[value [after EQ]]|[ev [target [ORD STEP]]]].
  - subst s; left; exists (Vint value), after; split; [reflexivity|].
    split; [exact (proj1 (invariant_facts _ _ _ _ _ _ INV))|].
    inversion INV; subst.
    match goal with H : routed _ _ _ _ _ _ |- _ => destruct H as [final [PATH END]] end.
    apply terminal_path in PATH; subst final; inversion END; subst; auto.
  - right; exists (original_event ev), target.
    split; [apply write_ordinary_control; exact ORD|constructor; exact STEP].
Qed.

Definition fault_zero_initial name k m := Callstate (Internal EntrySource.f_fault) [name] k m.

Lemma fault_zero_path (name : val) k m : is_call_cont k ->
  store_path failure_ge (fun after => after = m) (fault_zero_initial name k m) 2
    (Returnstate (Vint Int.zero) k m).
Proof.
  intros CALL.
  assert (CONT : call_cont k = k) by (destruct k; cbn in *; try contradiction; reflexivity).
  eapply store_next; [reflexivity| |].
  - apply function_entry_source_edge; constructor.
    + repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); apply list_norepet_nil.
    + repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); apply list_norepet_nil.
    + unfold list_disjoint, var_names; cbn; tauto.
    + constructor.
    + reflexivity.
  - eapply store_next; [reflexivity| |].
    + apply unchanged_store_edge.
      eapply edge_return; [apply value_int|reflexivity].
    + rewrite CONT; apply store_done; reflexivity.
Qed.

Theorem fault_zero_progress cell name m :
  procedure_progress failure_ge cell (fault_zero_initial name Kstop m)
    (fun value after => value = Vint Int.zero /\ after = m).
Proof.
  intros events s RUN.
  pose proof (fault_zero_path name Kstop m I) as PATH.
  destruct (source_path_caller_prefix _ _ _ _ _ _ PATH _ _ RUN)
    as [[n [state [remaining [_ [_ [SAME TAIL]]]]]]|[[n [after [_ [_ [SAME _]]]]]|[rest [_ AFTER]]]].
  - inversion SAME; subst state; inversion TAIL; subst.
    + left; eauto.
    + right; exists (original_event (source_step E0)), (live next); split.
      * unfold control_progress; cbn; repeat split; discriminate.
      * constructor; match goal with EDGE : store_edge _ _ _ |- _ =>
          destruct EDGE as [IN [REAL _]] end; apply internal; assumption.
  - discriminate.
  - inversion AFTER as [|before event middle tail target STEP REST]; subst.
    + left; eauto.
    + destruct (control_return_step _ _ _ _ _ _ STEP) as [EVENT TARGET]; subst middle.
      destruct (library_dead_steps _ _ _ _ _ REST) as [EMPTY TARGET]; discriminate.
Qed.

Theorem current_failure_write_progress q input m local le k :
  write_owned q input m ->
  live_progress failure_ge (cell_of q) (write_call_initial q (failure_write_cont local le k) m).
Proof.
  intros OWN; eapply call_live_progress; [exact I|apply current_write_progress; exact OWN|].
  intros value after POST; eapply source_path_live_progress;
    [apply failure_after_write_path|apply exit_live_progress].
Qed.

Lemma current_failure_short_progress base built local cell fd stage error short k :
  tls_ready cell base -> old_memory base built -> ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  live_progress failure_ge cell (failure_short_state local fd stage error short k built).
Proof.
  intros TLS OLD FRESH PACKET.
  change (live_progress failure_ge cell
    (plug_state (fault_zero_initial (Vptr short Ptrofs.zero) Kstop built)
      (failure_short_cont local fd stage error k))).
  eapply call_live_progress; [exact I|apply fault_zero_progress|].
  intros value after [VALUE AFTER]; subst value after.
  change (Vint Int.zero) with (Val.of_bool false).
  eapply source_path_live_progress; [apply failure_short_or_full_path with (cell:=cell)|].
  set (q := failure_request cell fd local 8).
  assert (OWN : write_owned q (firstn 8 (failure_packet stage error)) built).
  { apply (failure_packet_write_owned base built local cell fd stage error 8 TLS FRESH OLD PACKET); lia. }
  change (live_progress failure_ge cell
    (write_call_initial q (failure_write_cont local (failure_write_temps fd stage error false) k) built)).
  replace cell with (cell_of q) by (unfold q, failure_request; destruct cell; reflexivity).
  apply current_failure_write_progress with (input:=firstn 8 (failure_packet stage error)); exact OWN.
Qed.

Theorem current_failure_all_prefixes cell base fd stage error k :
  tls_ready cell base -> is_call_cont k ->
  live_progress failure_ge cell (failure_initial fd stage error k base).
Proof.
  intros TLS CALL.
  assert (DROP : exists drop, Genv.find_symbol failure_ge ___stringlit_8 = Some drop)
    by (eexists; vm_compute; reflexivity).
  assert (SHORT : exists short, Genv.find_symbol failure_ge ___stringlit_9 = Some short)
    by (eexists; vm_compute; reflexivity).
  destruct DROP as [drop DROP]; destruct SHORT as [short SHORT].
  destruct (failure_prepare_execution base fd stage error drop k CALL DROP)
    as [local [built [PATH [FRESH [OLD [RANGE PACKET]]]]]].
  eapply source_path_live_progress; [exact PATH|].
  change (live_progress failure_ge cell
    (plug_state (fault_zero_initial (Vptr drop Ptrofs.zero) Kstop built)
      (failure_drop_cont local fd stage error k))).
  eapply call_live_progress; [exact I|apply fault_zero_progress|].
  intros value after [VALUE AFTER]; subst value after.
  eapply source_path_live_progress; [apply failure_not_drop_path; exact SHORT|].
  exact (current_failure_short_progress base built local cell fd stage error short k TLS OLD FRESH PACKET).
Qed.

Theorem current_failure_never_returns cell base fd stage error events value after :
  tls_ready cell base ->
  ~ library_steps failure_ge cell (live (failure_initial fd stage error Kstop base)) events
    (live (Returnstate value Kstop after)).
Proof.
  intros TLS.
  exact (live_progress_never_returns failure_ge cell
    (failure_initial fd stage error Kstop base)
    (current_failure_all_prefixes cell base fd stage error Kstop TLS I)
    events value after).
Qed.
