(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The actual fork branch and parent return preserve their own observed FD events. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber StoreSteps LibraryMachine ProcessEffects WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceStructure NamespaceAllocation NamespacePaths NamespaceCaller
  NamespaceBorrow NamespaceMemory NamespaceTraceRegion NamespaceTraceEffects NamespaceChildResult.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Section CHILD_TAIL.
Variable scope : ChildScope.
Local Notation cell := (scope_cell scope).
Local Notation objects := (scope_storage scope).
Local Notation pair := (storage_pair objects).
Local Notation peer := (storage_peer objects).
Local Notation pid := (storage_pid objects).
Local Notation borrowed := (scope_borrowed scope).
Local Notation k := (scope_continuation scope).

Theorem child_parent_tail_trace le m first second failure reply returned :
  le!_failure = Some (Vint failure) -> 0<=Int.signed failure -> returned <> Int.zero ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m peer 0 = Some (Vint first) -> Mem.load Mint32 m pid 0 = Some (Vint returned) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 6
    (child_fork_log scope first second failure reply returned)
    (State f_create_entry_child (child_tail 10 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros FAILURE NONNEGATIVE NONZERO SEPARATE PRIVATE OWN INPUT PEER PID.
  destruct SEPARATE as [PAIR_TLS [PEER_TLS [PID_TLS [PEER_PAIR [PID_PAIR PEER_PID]]]]].
  destruct PRIVATE as [PAIR_PRIVATE [PEER_PRIVATE PID_PRIVATE]].
  eapply namespace_trace_store_path with (count:=2%nat) (remaining:=4%nat).
  - apply child_close_failure_source; exact FAILURE.
  - eapply namespace_trace_close.
    + apply entry_errno_ready_tls; exact (handoff_borrowed_errno _ _ _ INPUT).
    + intros closed after CLOSE.
      assert (READY : entry_errno_ready cell after).
      { eapply namespace_errno_ready_close; [exact (handoff_borrowed_errno _ _ _ INPUT)|exact CLOSE]. }
      assert (BORROWED : handoff_borrowed_input cell after borrowed).
      { eapply namespace_close_preserves_borrows; eassumption. }
      assert (STORAGE : child_storage cell objects after).
      { eapply child_storage_close; eassumption. }
      destruct STORAGE as [AFTER_ERRNO [PAIR REST]].
      destruct (Mem.range_perm_free _ _ _ _ PAIR) as [final FREE].
      assert (FREE_LIST : Mem.free_list after (blocks_of_env namespace_ge (child_env pair)) = Some final).
      { change (Mem.free_list after [(pair,0,8)] = Some final); cbn; rewrite FREE; reflexivity. }
      eapply namespace_trace_store_path with (count:=3%nat) (remaining:=0%nat).
      * apply child_finish_source; exact FREE_LIST.
      * apply namespace_trace_stop; eapply child_parent_result; [exact NONZERO|exact NONNEGATIVE| | |].
        -- eapply namespace_free_preserves_borrows;
             [exact BORROWED|exact PAIR_PRIVATE|exact PAIR_TLS|exact FREE].
        -- eapply namespace_free_preserves_load; [exact FREE|exact PEER_PAIR|].
           eapply namespace_close_preserves_load; eassumption.
        -- eapply namespace_free_preserves_load; [exact FREE|exact PID_PAIR|].
           eapply namespace_close_preserves_load; eassumption.
Qed.

Theorem child_select_tail_trace le m first second failure reply returned :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  le!_forked = Some (Vint returned) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m peer 0 = Some (Vint first) -> Mem.load Mint32 m pid 0 = Some (Vint returned) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 9
    (child_fork_log scope first second failure reply returned)
    (State f_create_entry_child (child_tail 9 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE FORKED SEPARATE PRIVATE OWN INPUT PEER PID.
  destruct (Int.eq_dec returned Int.zero) as [ZERO|NONZERO].
  - subst returned; eapply namespace_trace_weaken with (n:=3%nat); [|lia].
    eapply namespace_trace_store_path with (count:=3%nat) (remaining:=0%nat).
    + destruct REGISTERS as [I [O [E [P C]]]].
      eapply child_select_guest_source with (input:=scope_input scope) (output:=scope_output scope)
        (errors:=scope_errors scope) (failure:=failure);
        [exact FORKED|exact I|exact O|exact E|exact FAILURE].
    + apply namespace_trace_stop; eapply child_guest_result; eassumption.
  - eapply namespace_trace_store_path with (count:=3%nat) (remaining:=6%nat).
    + eapply child_select_parent_source; eassumption.
    + eapply child_parent_tail_trace; eassumption.
Qed.

Theorem child_publish_pid_trace le m first second failure reply returned :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  le!_forked = Some (Vint returned) ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m peer 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 12
    (child_fork_log scope first second failure reply returned)
    (State f_create_entry_child (child_tail 8 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE FORKED SEPARATE PRIVATE OWN INPUT PEER.
  destruct (child_pid_store_exists _ _ _ returned OWN) as [after STORE].
  assert (PID_VALUE : Mem.load Mint32 after pid 0 = Some (Vint returned)).
  { erewrite Mem.load_store_same by exact STORE; reflexivity. }
  assert (PID_TLS : pid <> tls_block cell).
  { destruct SEPARATE as [A [B [C REST]]]; exact C. }
  assert (PID_PRIVATE : ~In pid (handoff_borrowed_blocks borrowed)).
  { destruct PRIVATE as [A [B C]]; exact C. }
  destruct (namespace_store_storage _ _ _ _ _ _ _ _ _ OWN SEPARATE INPUT PID_PRIVATE PID_TLS STORE)
    as [STORAGE BORROWED].
  eapply namespace_trace_store_path with (count:=3%nat) (remaining:=9%nat).
  - apply child_publish_pid_source with (object:=pid) (offset:=Ptrofs.zero) (returned:=returned).
    + exact FORKED.
    + exact (proj2 (proj2 (proj2 (proj2 REGISTERS)))).
    + exact STORE.
  - eapply child_select_tail_trace; try eassumption.
    rewrite (Mem.load_store_other _ _ _ _ _ _ STORE) by
      (left; destruct SEPARATE as [A [B [C [D [E F]]]]]; exact F); exact PEER.
Qed.

Theorem child_fork_return_trace le m first second failure reply returned :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m peer 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 16
    (child_fork_log scope first second failure reply returned)
    (Returnstate (Vint returned) (child_fork_cont pair le k) m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE OWN INPUT PEER.
  eapply namespace_trace_store_path with (count:=4%nat) (remaining:=12%nat).
  - apply child_fork_return_source.
  - eapply child_publish_pid_trace; try eassumption.
    + unfold child_fork_return_env; child_scope_registers.
    + unfold child_fork_return_env; WriteAll.lookup.
    + unfold child_fork_return_env; apply PTree.gss.
Qed.

Theorem child_fork_tail_trace le m first second failure reply :
  child_scope_registers scope le -> le!_failure = Some (Vint failure) -> 0<=Int.signed failure ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  Mem.load Mint32 m peer 0 = Some (Vint first) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 20
    (child_signal_log scope first second failure reply)
    (State f_create_entry_child (child_tail 7 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros REGISTERS FAILURE NONNEGATIVE SEPARATE PRIVATE OWN INPUT PEER.
  eapply namespace_trace_store_path with (count:=3%nat) (remaining:=17%nat).
  - apply child_fork_source.
  - eapply namespace_trace_fork; [exact (handoff_borrowed_errno _ _ _ INPUT)|].
    intros returned after FRAME READY.
    eapply child_fork_return_trace; try eassumption.
    + eapply child_storage_partial; eassumption.
    + eapply namespace_errno_effect_preserves_borrows; eassumption.
    + eapply namespace_partial_preserves_load; [exact FRAME| |exact PEER].
      destruct SEPARATE as [A [B REST]]; exact B.
Qed.
End CHILD_TAIL.
