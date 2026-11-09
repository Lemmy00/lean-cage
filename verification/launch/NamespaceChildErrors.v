(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.control: Every local failure path reaches a positive setup error or loses execution. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber StoreSteps LibraryMachine ProcessEffects WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceStructure NamespaceAllocation NamespacePaths NamespaceCaller
  NamespaceFailure NamespaceBorrow NamespaceMemory NamespaceTraceRegion NamespaceTraceEffects NamespaceChildResult.
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

Lemma child_error_return_trace_to log m start count error :
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  1 <= Int.signed error <= 4095 ->
  child_before_fork scope log ->
  (forall after, Mem.free m pair 0 8 = Some after ->
    store_path namespace_ge (fun current=>current=m \/ current=after) start count
      (Returnstate (Vint error) (call_cont k) after)) ->
  namespace_trace_region namespace_ge cell (result) count log start.
Proof.
  intros [TLS REST] [PRIVATE MORE] [ERRNO [OWN MORE_OWN]] INPUT RANGE NOFORK PATH.
  destruct (Mem.range_perm_free _ _ _ _ OWN) as [after FREE].
  replace count with (count+0)%nat by lia.
  eapply namespace_trace_store_path with (count:=count) (remaining:=0%nat).
  - apply PATH; exact FREE.
  - apply namespace_trace_stop,accept_setup_error; [exact RANGE| |exact NOFORK].
    eapply namespace_free_preserves_borrows; eassumption.
Qed.

Lemma child_error_call_trace_to log m suffix remaining :
  handoff_borrowed_input cell m borrowed -> is_call_cont suffix ->
  (forall error, 1<=Int.signed error<=4095 ->
    namespace_trace_region namespace_ge cell (result) remaining log
      (Returnstate (Vint error) suffix m)) ->
  namespace_trace_region namespace_ge cell (result) (34+remaining)%nat log
    (Callstate (Internal f_error_number) [] suffix m).
Proof.
  intros INPUT CALL RETURN.
  destruct (handoff_borrowed_errno _ _ _ INPUT) as [raw ERRNO].
  eapply namespace_trace_weaken with (n:=(source_length raw+remaining)%nat).
  - apply namespace_trace_error; [exact ERRNO|exact CALL|apply RETURN,normalize_range].
  - unfold source_length; destruct (positive raw); [destruct (bounded raw)|]; lia.
Qed.

Theorem child_socket_errno_trace_to log le m returned :
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  child_before_fork scope log ->
  namespace_trace_region namespace_ge cell (result) 37 log
    (Callstate (Internal f_error_number) [] (child_socket_error_cont pair le returned k) m).
Proof.
  intros SEPARATE PRIVATE OWN INPUT NOFORK.
  apply child_error_call_trace_to; [exact INPUT|exact I|]. intros error RANGE.
  eapply child_error_return_trace_to; try eassumption.
  intros after FREE; apply child_socket_error_return_source.
  change (Mem.free_list m [(pair,0,8)] = Some after); cbn; rewrite FREE; reflexivity.
Qed.

Theorem child_duplicate_errno_trace_to log le m first :
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  child_before_fork scope log ->
  namespace_trace_region namespace_ge cell (result) 37 log
    (Callstate (Internal f_error_number) [] (child_duplicate_error_cont pair le first k) m).
Proof.
  intros SEPARATE PRIVATE OWN INPUT NOFORK.
  apply child_error_call_trace_to; [exact INPUT|exact I|]. intros error RANGE.
  eapply child_error_return_trace_to; try eassumption.
  intros after FREE; apply child_duplicate_error_return_source.
  change (Mem.free_list m [(pair,0,8)] = Some after); cbn; rewrite FREE; reflexivity.
Qed.

Theorem child_mask_errno_trace_to log le m returned failure first :
  le!_failure = Some (Vint failure) ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  child_before_fork scope log ->
  namespace_trace_region namespace_ge cell (result) 52 log
    (Callstate (Internal f_error_number) [] (child_mask_error_cont pair le returned k) m).
Proof.
  intros FAILURE FIRST SEPARATE PRIVATE OWN INPUT NOFORK.
  apply child_error_call_trace_to; [exact INPUT|exact I|]. intros error RANGE.
  eapply namespace_trace_store_path with (count:=6%nat) (remaining:=12%nat).
  - apply child_mask_error_capture_source; exact FAILURE.
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
      * apply child_mask_close_failure_return_source.
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
             [exact SEPARATE|exact PRIVATE|exact OWN2|exact INPUT2|exact RANGE| |].
           ++ apply child_before_fork_extend; [apply child_before_fork_extend; [exact NOFORK|exact I]|exact I].
           ++ intros after FREE; apply child_mask_error_return_source.
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

Lemma child_error_return_trace log m start count error :
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  1 <= Int.signed error <= 4095 ->
  child_before_fork scope log ->
  (forall after, Mem.free m pair 0 8 = Some after ->
    store_path namespace_ge (fun current=>current=m \/ current=after) start count
      (Returnstate (Vint error) (call_cont k) after)) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) count log start.
Proof. intros;eapply child_error_return_trace_to;eauto 12 using child_setup_error_result. Qed.
Lemma child_error_call_trace log m suffix remaining :
  handoff_borrowed_input cell m borrowed -> is_call_cont suffix ->
  (forall error, 1<=Int.signed error<=4095 ->
    namespace_trace_region namespace_ge cell (ChildResult scope) remaining log
      (Returnstate (Vint error) suffix m)) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) (34+remaining)%nat log
    (Callstate (Internal f_error_number) [] suffix m).
Proof. intros;eapply child_error_call_trace_to;eauto 12 using child_setup_error_result. Qed.
Theorem child_socket_errno_trace log le m returned :
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  child_before_fork scope log ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 37 log
    (Callstate (Internal f_error_number) [] (child_socket_error_cont pair le returned k) m).
Proof. intros;eapply child_socket_errno_trace_to;eauto 12 using child_setup_error_result. Qed.
Theorem child_duplicate_errno_trace log le m first :
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  child_before_fork scope log ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 37 log
    (Callstate (Internal f_error_number) [] (child_duplicate_error_cont pair le first k) m).
Proof. intros;eapply child_duplicate_errno_trace_to;eauto 12 using child_setup_error_result. Qed.
Theorem child_mask_errno_trace log le m returned failure first :
  le!_failure = Some (Vint failure) ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  child_before_fork scope log ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 52 log
    (Callstate (Internal f_error_number) [] (child_mask_error_cont pair le returned k) m).
Proof. intros;eapply child_mask_errno_trace_to;eauto 12 using child_setup_error_result. Qed.
End PRESERVED_CHILD_API.
