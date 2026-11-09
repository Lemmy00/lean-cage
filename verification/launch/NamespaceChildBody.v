(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The complete local helper reaches its justified source leaf or loses execution. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber StoreSteps LibraryMachine ProcessEffects WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths
  NamespaceBorrow NamespaceMemory NamespaceRegion NamespaceTraceRegion NamespaceTraceEffects NamespaceChildResult
  NamespaceChildErrors NamespaceChildChannel.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Section CHILD_BODY.
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


Theorem child_socket_return_trace_to le m returned first second :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  (returned=Int.zero -> Mem.load Mint32 m pair 0 = Some (Vint first) /\
    Mem.load Mint32 m pair 4 = Some (Vint second)) ->
  namespace_trace_region namespace_ge cell (result) 105
    (scope_history scope ++ [namespace_paired (Int.repr 1) (Int.repr 524289) Int.zero
      pair Ptrofs.zero returned first second])
    (Returnstate (Vint returned) (child_socket_cont pair le k) m).
Proof.
  intros REGISTERS SEPARATE PRIVATE OWN INPUT CELLS.
  destruct (Int.eq_dec returned Int.zero) as [ZERO|NONZERO].
  - subst returned; destruct (CELLS eq_refl) as [FIRST SECOND].
    eapply namespace_trace_weaken with (n:=103%nat); [|lia].
    eapply namespace_trace_store_path with (count:=4%nat) (remaining:=99%nat).
    + apply child_socket_success_source.
    + eapply child_duplicate_tail_trace_to; try eassumption; child_scope_registers.
  - eapply namespace_trace_weaken with (n:=42%nat); [|lia].
    eapply namespace_trace_store_path with (count:=5%nat) (remaining:=37%nat).
    + apply child_socket_failure_source; exact NONZERO.
    + eapply child_socket_errno_trace_to; try eassumption.
      apply child_before_fork_extend; [apply child_before_fork_start|exact I].
Qed.

Theorem complete_child_body_trace_to le m :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  namespace_trace_region namespace_ge cell (result) 109
    (scope_history scope)
    (State f_create_entry_child (fn_body f_create_entry_child) k (child_env pair) le m).
Proof.
  intros REGISTERS SEPARATE PRIVATE OWN INPUT.
  eapply namespace_trace_store_path with (count:=3%nat) (remaining:=106%nat).
  - apply child_socket_source.
  - eapply namespace_trace_pair.
    + apply child_pair_is_writable with (cell:=cell) (objects:=objects); exact OWN.
    + exact (handoff_borrowed_errno _ _ _ INPUT).
    + intros returned first second after EFFECT READY.
      assert (PAIR_TLS : pair<>tls_block cell) by exact (proj1 SEPARATE).
      assert (PAIR_PRIVATE : ~In pair (handoff_borrowed_blocks borrowed)) by exact (proj1 PRIVATE).
      eapply child_socket_return_trace_to; try eassumption.
      * eapply child_storage_permissions; [exact OWN|exact READY|].
        eapply namespace_pair_permissions; exact EFFECT.
      * eapply namespace_pair_preserves_borrows;
          [exact INPUT|exact PAIR_PRIVATE|exact PAIR_TLS|exact EFFECT|exact READY].
      * intros ZERO; subst returned.
        exact (namespace_pair_returned_cells _ _ _ _ _ _ _ PAIR_TLS EFFECT).
Qed.

Theorem complete_child_body_same_run_to le m events target :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  namespace_steps namespace_ge cell
    (live (State f_create_entry_child (fn_body f_create_entry_child) k (child_env pair) le m)) events target ->
  ((namespace_cost events<=110)%nat /\ namespace_no_images events /\
    (forall state, target=live state -> exists remaining,
      namespace_trace_region namespace_ge cell (result) remaining
        (scope_history scope++namespace_fd_events events) state)) \/
  (exists prefix endpoint rest, events=prefix++rest /\
    namespace_no_images prefix /\
    namespace_steps namespace_ge cell
      (live (State f_create_entry_child (fn_body f_create_entry_child) k (child_env pair) le m))
      prefix (live endpoint) /\
    result (scope_history scope++namespace_fd_events prefix) endpoint /\
    namespace_steps namespace_ge cell (live endpoint) rest target).
Proof.
  intros REGISTERS SEPARATE PRIVATE OWN INPUT RUN.
  destruct (namespace_trace_execution_split _ _ _ _ _ _
    (complete_child_body_trace_to le m REGISTERS SEPARATE PRIVATE OWN INPUT) _ _ RUN)
    as [PREFIX|[prefix [endpoint [rest [EVENTS [COST [NOIMAGES [PRE [RESULT POST]]]]]]]]].
  - left; exact PREFIX.
  - right; exists prefix,endpoint,rest; auto.
Qed.
End CHILD_BODY.

Section PRESERVED_CHILD_API.
Variable scope : ChildScope.
Local Notation cell := (scope_cell scope).
Local Notation objects := (scope_storage scope).
Local Notation pair := (storage_pair objects).
Local Notation borrowed := (scope_borrowed scope).
Local Notation k := (scope_continuation scope).

Theorem child_socket_return_trace le m returned first second :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  (returned=Int.zero -> Mem.load Mint32 m pair 0 = Some (Vint first) /\
    Mem.load Mint32 m pair 4 = Some (Vint second)) ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 105
    (scope_history scope ++ [namespace_paired (Int.repr 1) (Int.repr 524289) Int.zero
      pair Ptrofs.zero returned first second])
    (Returnstate (Vint returned) (child_socket_cont pair le k) m).
Proof. intros;eapply child_socket_return_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem complete_child_body_trace le m :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  namespace_trace_region namespace_ge cell (ChildResult scope) 109
    (scope_history scope)
    (State f_create_entry_child (fn_body f_create_entry_child) k (child_env pair) le m).
Proof. intros;eapply complete_child_body_trace_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
Theorem complete_child_body_same_run le m events target :
  child_scope_registers scope le ->
  child_storage_separate cell objects -> child_scope_private scope ->
  child_storage cell objects m -> handoff_borrowed_input cell m borrowed ->
  namespace_steps namespace_ge cell
    (live (State f_create_entry_child (fn_body f_create_entry_child) k (child_env pair) le m)) events target ->
  ((namespace_cost events<=110)%nat /\ namespace_no_images events /\
    (forall state, target=live state -> exists remaining,
      namespace_trace_region namespace_ge cell (ChildResult scope) remaining
        (scope_history scope++namespace_fd_events events) state)) \/
  (exists prefix endpoint rest, events=prefix++rest /\
    namespace_no_images prefix /\
    namespace_steps namespace_ge cell
      (live (State f_create_entry_child (fn_body f_create_entry_child) k (child_env pair) le m))
      prefix (live endpoint) /\
    ChildResult scope (scope_history scope++namespace_fd_events prefix) endpoint /\
    namespace_steps namespace_ge cell (live endpoint) rest target).
Proof. intros;eapply complete_child_body_same_run_to;eauto 12 using child_setup_error_result, EntryNamespace.NamespaceChildTail.child_fork_tail_trace. Qed.
End PRESERVED_CHILD_API.
