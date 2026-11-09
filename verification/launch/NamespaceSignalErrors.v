(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.control: Every local failure path reaches a positive setup error or loses execution. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber StoreSteps LibraryMachine ProcessEffects WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceStructure NamespaceAllocation NamespacePaths NamespaceCaller
  NamespaceFailure NamespaceSignalFailure NamespaceChildErrors NamespaceBorrow NamespaceMemory NamespaceTraceRegion NamespaceTraceEffects NamespaceChildResult.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Section CHILD_ERRORS.
Variable scope : ChildScope.
Variable result : list NamespaceMachine.namespace_event -> Clight.state -> Prop.
Hypothesis accept_setup_error : forall log error after,
  1<=Int.signed error<=4095 ->
  handoff_borrowed_input(scope_cell scope)after(scope_borrowed scope) ->
  child_before_fork scope log ->
  result log(Returnstate(Vint error)(call_cont(scope_continuation scope))after).

Local Notation cell := (scope_cell scope).
Local Notation objects := (scope_storage scope).
Local Notation pair := (storage_pair objects).
Local Notation borrowed := (scope_borrowed scope).
Local Notation k := (scope_continuation scope).

Theorem child_default_errno_trace_to log le m returned failure first :
  le!_failure = Some (Vint failure) ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  child_before_fork scope log ->
  namespace_trace_region namespace_ge cell (result) 52 log
    (Callstate (Internal f_error_number) [] (child_default_error_cont pair le returned k) m).
Proof.
  intros FAILURE FIRST SEPARATE PRIVATE OWN INPUT NOFORK.
  apply child_error_call_trace_to; [exact INPUT|exact I|]. intros error RANGE.
  eapply namespace_trace_store_path with (count:=6%nat) (remaining:=12%nat).
  - apply child_default_error_capture_source; exact FAILURE.
  - eapply namespace_trace_close.
    + apply entry_errno_ready_tls; exact (handoff_borrowed_errno _ _ _ INPUT).
    + intros closed1 m1 CLOSE1.
      assert (READY1 : entry_errno_ready cell m1).
      { eapply namespace_errno_ready_close; [exact (handoff_borrowed_errno _ _ _ INPUT)|exact CLOSE1]. }
      assert (INPUT1 : handoff_borrowed_input cell m1 borrowed).
      { eapply namespace_close_preserves_borrows; eassumption. }
      assert (OWN1 : child_storage cell objects m1).
      { eapply child_storage_close; eassumption. }
      eapply namespace_trace_store_path with (count:=7%nat) (remaining:=4%nat).
      * apply child_default_close_failure_return_source.
        eapply namespace_close_preserves_load; [exact CLOSE1| |exact FIRST].
        exact (proj1 SEPARATE).
      * eapply namespace_trace_close.
        -- apply entry_errno_ready_tls; exact READY1.
        -- intros closed2 m2 CLOSE2.
           assert (READY2 : entry_errno_ready cell m2).
           { eapply namespace_errno_ready_close; [exact READY1|exact CLOSE2]. }
           assert (INPUT2 : handoff_borrowed_input cell m2 borrowed).
           { eapply namespace_close_preserves_borrows; [exact INPUT1|exact CLOSE2|exact READY2]. }
           assert (OWN2 : child_storage cell objects m2).
           { eapply child_storage_close; [exact OWN1|exact CLOSE2|exact READY2]. }
           eapply child_error_return_trace_to;
             [exact accept_setup_error|exact SEPARATE|exact PRIVATE|exact OWN2|exact INPUT2|exact RANGE| |].
           ++ apply child_before_fork_extend; [apply child_before_fork_extend; [exact NOFORK|exact I]|exact I].
           ++ intros after FREE; apply child_default_error_return_source.
              change (Mem.free_list m2 [(pair,0,8)] = Some after); cbn; rewrite FREE; reflexivity.
Qed.
End CHILD_ERRORS.

Section PRESERVED_CHILD_API.
Variable scope : ChildScope.
Local Notation cell := (scope_cell scope).
Local Notation objects := (scope_storage scope).
Local Notation pair := (storage_pair objects).
Local Notation borrowed := (scope_borrowed scope).
Local Notation k := (scope_continuation scope).

Theorem child_default_errno_trace log le m returned failure first :
  le!_failure = Some (Vint failure) ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  child_before_fork scope log ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 52 log
    (Callstate (Internal f_error_number) [] (child_default_error_cont pair le returned k) m).
Proof. intros;eapply child_default_errno_trace_to;eauto 12 using child_setup_error_result. Qed.
End PRESERVED_CHILD_API.
