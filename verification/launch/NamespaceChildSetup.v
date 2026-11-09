(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Mask and explicit-reap acknowledgements precede the actual local fork. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber StoreSteps LibraryMachine ProcessEffects WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceStructure NamespaceAllocation NamespacePaths NamespaceFailure
  NamespaceSignalFailure NamespaceBorrow NamespaceMemory NamespaceTraceRegion NamespaceTraceEffects
  NamespaceChildResult NamespaceChildTail NamespaceChildErrors NamespaceSignalErrors.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Section CHILD_SETUP.
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
Local Notation peer := (storage_peer objects).
Local Notation borrowed := (scope_borrowed scope).
Local Notation k := (scope_continuation scope).
Hypothesis fork_tail : forall le m first second failure reply,
  child_scope_registers scope le ->le!_failure=Some(Vint failure) ->0<=Int.signed failure ->
  child_storage_separate cell objects ->child_scope_private scope ->
  child_storage cell objects m ->handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m (storage_peer objects)0=Some(Vint first) ->
  namespace_trace_region namespace_ge cell result 20(child_signal_log scope first second failure reply)
    (State f_create_entry_child(child_tail 7(fn_body f_create_entry_child))k(child_env pair)le m).


Theorem child_publish_peer_trace_to le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (result) 26
    (child_signal_log scope first second failure reply)
    (State f_create_entry_child (child_tail 6 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE OWN INPUT FIRST.
  destruct (child_peer_store_exists _ _ _ first OWN) as [after STORE].
  assert (PEER_TLS : peer<>tls_block cell) by (destruct SEPARATE as [A [B REST]]; exact B).
  assert (PEER_PRIVATE : ~In peer (handoff_borrowed_blocks borrowed))
    by (destruct PRIVATE as [A [B REST]]; exact B).
  destruct (namespace_store_storage _ _ _ _ _ _ _ _ _ OWN SEPARATE INPUT PEER_PRIVATE PEER_TLS STORE)
    as [STORAGE BORROWED].
  eapply namespace_trace_store_path with (count:=6%nat) (remaining:=20%nat).
  - apply child_publish_peer_source with (first:=first) (peer:=peer) (offset:=Ptrofs.zero).
    + exact FIRST.
    + exact (proj1 (proj2 (proj2 (proj2 REGISTERS)))).
    + exact STORE.
  - eapply fork_tail; try eassumption.
    + unfold child_publish_peer_env; child_scope_registers.
    + unfold child_publish_peer_env; WriteAll.lookup.
    + erewrite Mem.load_store_same by exact STORE; reflexivity.
Qed.

Theorem child_default_return_trace_to le m log_first second failure reply returned :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint log_first) ->
  namespace_trace_region namespace_ge cell (result) 60
    (child_mask_log scope log_first second failure reply ++ [NamespaceMachine.namespace_defaulted (Int.repr 17) returned])
    (Returnstate (Vlong returned) (child_default_cont pair le k) m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE OWN INPUT FIRST.
  destruct (Int64.eq_dec returned Int64.zero) as [ZERO|NONZERO].
  - subst returned; eapply namespace_trace_weaken with (n:=30%nat); [|lia].
    eapply namespace_trace_store_path with (count:=4%nat) (remaining:=26%nat).
    + apply child_default_success_source.
    + eapply child_publish_peer_trace_to; try eassumption.
      * child_scope_registers.
      * WriteAll.lookup.
  - eapply namespace_trace_weaken with (n:=58%nat); [|lia].
    eapply namespace_trace_store_path with (count:=6%nat) (remaining:=52%nat).
    + apply child_default_failure_source; exact NONZERO.
    + eapply child_default_errno_trace_to; try eassumption.
      apply child_before_fork_extend; [apply child_mask_before_fork|exact I].
Qed.

Theorem child_default_tail_trace_to le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (result) 64
    (child_mask_log scope first second failure reply)
    (State f_create_entry_child (child_tail 5 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE OWN INPUT FIRST.
  eapply namespace_trace_store_path with (count:=3%nat) (remaining:=61%nat).
  - apply child_default_source.
  - eapply namespace_trace_default; [exact (handoff_borrowed_errno _ _ _ INPUT)|].
    intros returned after FRAME READY.
    eapply child_default_return_trace_to; try eassumption.
    + eapply child_storage_partial; eassumption.
    + eapply namespace_errno_effect_preserves_borrows; eassumption.
    + eapply namespace_partial_preserves_load; [exact FRAME|exact (proj1 SEPARATE)|exact FIRST].
Qed.

Theorem child_mask_return_trace_to le m first second failure reply returned :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (result) 70
    (child_closed_log scope first second failure reply ++ [NamespaceMachine.namespace_masked Int64.mone returned])
    (Returnstate (Vlong returned) (child_mask_cont pair le k) m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE OWN INPUT FIRST.
  destruct (Int64.eq_dec returned Int64.zero) as [ZERO|NONZERO].
  - subst returned; eapply namespace_trace_weaken with (n:=68%nat); [|lia].
    eapply namespace_trace_store_path with (count:=4%nat) (remaining:=64%nat).
    + apply child_mask_success_source.
    + eapply child_default_tail_trace_to; try eassumption.
      * child_scope_registers.
      * WriteAll.lookup.
  - eapply namespace_trace_weaken with (n:=58%nat); [|lia].
    eapply namespace_trace_store_path with (count:=6%nat) (remaining:=52%nat).
    + apply child_mask_failure_source; exact NONZERO.
    + eapply child_mask_errno_trace_to; try eassumption.
      apply child_before_fork_extend; [apply child_closed_before_fork|exact I].
Qed.

Theorem child_mask_tail_trace_to le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (result) 74
    (child_closed_log scope first second failure reply)
    (State f_create_entry_child (child_tail 4 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE OWN INPUT FIRST.
  eapply namespace_trace_store_path with (count:=3%nat) (remaining:=71%nat).
  - apply child_mask_source.
  - eapply namespace_trace_mask; [exact (handoff_borrowed_errno _ _ _ INPUT)|].
    intros returned after FRAME READY.
    eapply child_mask_return_trace_to; try eassumption.
    + eapply child_storage_partial; eassumption.
    + eapply namespace_errno_effect_preserves_borrows; eassumption.
    + eapply namespace_partial_preserves_load; [exact FRAME|exact (proj1 SEPARATE)|exact FIRST].
Qed.
End CHILD_SETUP.

Section PRESERVED_CHILD_API.
Variable scope : ChildScope.
Local Notation cell := (scope_cell scope).
Local Notation objects := (scope_storage scope).
Local Notation pair := (storage_pair objects).
Local Notation peer := (storage_peer objects).
Local Notation borrowed := (scope_borrowed scope).
Local Notation k := (scope_continuation scope).

Theorem child_publish_peer_trace le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 26
    (child_signal_log scope first second failure reply)
    (State f_create_entry_child (child_tail 6 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof. intros;eapply child_publish_peer_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem child_default_return_trace le m log_first second failure reply returned :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint log_first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 60
    (child_mask_log scope log_first second failure reply ++ [NamespaceMachine.namespace_defaulted (Int.repr 17) returned])
    (Returnstate (Vlong returned) (child_default_cont pair le k) m).
Proof. intros;eapply child_default_return_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem child_default_tail_trace le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 64
    (child_mask_log scope first second failure reply)
    (State f_create_entry_child (child_tail 5 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof. intros;eapply child_default_tail_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem child_mask_return_trace le m first second failure reply returned :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 70
    (child_closed_log scope first second failure reply ++ [NamespaceMachine.namespace_masked Int64.mone returned])
    (Returnstate (Vlong returned) (child_mask_cont pair le k) m).
Proof. intros;eapply child_mask_return_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem child_mask_tail_trace le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 74
    (child_closed_log scope first second failure reply)
    (State f_create_entry_child (child_tail 4 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof. intros;eapply child_mask_tail_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
End PRESERVED_CHILD_API.
