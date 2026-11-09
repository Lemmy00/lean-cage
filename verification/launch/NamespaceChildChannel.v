(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual pair cells feed the duplicate, close and guarded setup path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber StoreSteps LibraryMachine ProcessEffects WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths
  NamespaceCaller NamespaceFailure NamespaceBorrow NamespaceMemory NamespaceTraceRegion NamespaceTraceEffects
  NamespaceChildResult NamespaceChildErrors NamespaceChildSetup.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Section CHILD_CHANNEL.
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
Hypothesis fork_tail : forall le m first second failure reply,
  child_scope_registers scope le ->le!_failure=Some(Vint failure) ->0<=Int.signed failure ->
  child_storage_separate cell objects ->child_scope_private scope ->
  child_storage cell objects m ->handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m (storage_peer objects)0=Some(Vint first) ->
  namespace_trace_region namespace_ge cell result 20(child_signal_log scope first second failure reply)
    (State f_create_entry_child(child_tail 7(fn_body f_create_entry_child))k(child_env pair)le m).


Theorem child_check_duplicate_trace_to le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (result) 80
    (child_closed_log scope first second failure reply)
    (State f_create_entry_child (child_tail 3 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS FAILURE SEPARATE PRIVATE OWN INPUT FIRST.
  destruct (zlt (Int.signed failure) 0) as [NEGATIVE|NONNEGATIVE].
  - eapply namespace_trace_weaken with (n:=49%nat); [|lia].
    eapply namespace_trace_store_path with (count:=7%nat) (remaining:=42%nat).
    + eapply child_duplicate_failure_source; eassumption.
    + eapply namespace_trace_close.
      * apply entry_errno_ready_tls; exact (handoff_borrowed_errno _ _ _ INPUT).
      * intros closed after CLOSE.
        assert (READY : entry_errno_ready cell after).
        { eapply namespace_errno_ready_close; [exact (handoff_borrowed_errno _ _ _ INPUT)|exact CLOSE]. }
        eapply namespace_trace_store_path with (count:=4%nat) (remaining:=37%nat).
        -- apply child_duplicate_cleanup_return_source.
        -- eapply child_duplicate_errno_trace_to; try eassumption.
           ++ eapply child_storage_close; eassumption.
           ++ eapply namespace_close_preserves_borrows; eassumption.
           ++ apply child_before_fork_extend; [apply child_closed_before_fork|exact I].
  - eapply namespace_trace_weaken with (n:=77%nat); [|lia].
    eapply namespace_trace_store_path with (count:=3%nat) (remaining:=74%nat).
    + apply child_duplicate_nonnegative_source with (failure:=failure); [exact FAILURE|lia].
    + eapply child_mask_tail_trace_to; try eassumption; lia.
Qed.

Theorem child_close_original_trace_to le m first second failure :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) -> Mem.load Mint32 m pair 4 = Some (Vint second) ->
  namespace_trace_region namespace_ge cell (result) 88
    (child_duplicate_log scope first second failure)
    (State f_create_entry_child (child_tail 2 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS FAILURE SEPARATE PRIVATE OWN INPUT FIRST SECOND.
  eapply namespace_trace_store_path with (count:=5%nat) (remaining:=83%nat).
  - apply child_close_original_source; exact SECOND.
  - eapply namespace_trace_close.
    + apply entry_errno_ready_tls; exact (handoff_borrowed_errno _ _ _ INPUT).
    + intros reply after CLOSE.
      assert (READY : entry_errno_ready cell after).
      { eapply namespace_errno_ready_close; [exact (handoff_borrowed_errno _ _ _ INPUT)|exact CLOSE]. }
      eapply namespace_trace_store_path with (count:=2%nat) (remaining:=80%nat).
      * apply child_close_original_return_source.
      * eapply child_check_duplicate_trace_to; try eassumption.
        -- unfold child_original_close_env; child_scope_registers.
        -- unfold child_original_close_env; WriteAll.lookup.
        -- eapply child_storage_close; eassumption.
        -- eapply namespace_close_preserves_borrows; eassumption.
        -- eapply namespace_close_preserves_load; [exact CLOSE|exact (proj1 SEPARATE)|exact FIRST].
Qed.

Theorem child_duplicate_return_trace_to le m first second failure :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) -> Mem.load Mint32 m pair 4 = Some (Vint second) ->
  namespace_trace_region namespace_ge cell (result) 92
    (child_duplicate_log scope first second failure)
    (Returnstate (Vint failure) (child_duplicate_cont pair le second k) m).
Proof.
  intros REGISTERS SEPARATE PRIVATE OWN INPUT FIRST SECOND.
  eapply namespace_trace_store_path with (count:=4%nat) (remaining:=88%nat).
  - apply child_duplicate_return_source.
  - eapply child_close_original_trace_to; try eassumption.
    + unfold child_duplicate_return_env,child_duplicate_call_env; child_scope_registers.
    + unfold child_duplicate_return_env; apply PTree.gss.
Qed.

Theorem child_duplicate_tail_trace_to le m first second :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) -> Mem.load Mint32 m pair 4 = Some (Vint second) ->
  namespace_trace_region namespace_ge cell (result) 99
    (child_pair_log scope first second)
    (State f_create_entry_child (child_tail 1 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS SEPARATE PRIVATE OWN INPUT FIRST SECOND.
  eapply namespace_trace_store_path with (count:=6%nat) (remaining:=93%nat).
  - apply child_duplicate_source; exact SECOND.
  - eapply namespace_trace_duplicate; [exact (handoff_borrowed_errno _ _ _ INPUT)|].
    intros failure after FRAME READY.
    eapply child_duplicate_return_trace_to; try eassumption.
    + eapply child_storage_partial; eassumption.
    + eapply namespace_errno_effect_preserves_borrows; eassumption.
    + eapply namespace_partial_preserves_load; [exact FRAME|exact (proj1 SEPARATE)|exact FIRST].
    + eapply namespace_partial_preserves_load; [exact FRAME|exact (proj1 SEPARATE)|exact SECOND].
Qed.
End CHILD_CHANNEL.

Section PRESERVED_CHILD_API.
Variable scope : ChildScope.
Local Notation cell := (scope_cell scope).
Local Notation objects := (scope_storage scope).
Local Notation pair := (storage_pair objects).
Local Notation borrowed := (scope_borrowed scope).
Local Notation k := (scope_continuation scope).

Theorem child_check_duplicate_trace le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 80
    (child_closed_log scope first second failure reply)
    (State f_create_entry_child (child_tail 3 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof. intros;eapply child_check_duplicate_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem child_close_original_trace le m first second failure :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) -> Mem.load Mint32 m pair 4 = Some (Vint second) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 88
    (child_duplicate_log scope first second failure)
    (State f_create_entry_child (child_tail 2 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof. intros;eapply child_close_original_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem child_duplicate_return_trace le m first second failure :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) -> Mem.load Mint32 m pair 4 = Some (Vint second) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 92
    (child_duplicate_log scope first second failure)
    (Returnstate (Vint failure) (child_duplicate_cont pair le second k) m).
Proof. intros;eapply child_duplicate_return_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem child_duplicate_tail_trace le m first second :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) -> Mem.load Mint32 m pair 4 = Some (Vint second) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 99
    (child_pair_log scope first second)
    (State f_create_entry_child (child_tail 1 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof. intros;eapply child_duplicate_tail_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
End PRESERVED_CHILD_API.
