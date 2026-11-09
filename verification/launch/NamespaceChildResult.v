(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: A local child result carries its exact source-observed channel/fork prefix. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffInput.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceAllocation NamespacePaths NamespaceMemory.
Import ListNotations.
Open Scope Z_scope.

Record ChildScope := {
  scope_cell : tls;
  scope_storage : ChildStorage;
  scope_borrowed : HandoffBorrowed;
  scope_input : int;
  scope_output : int;
  scope_errors : int;
  scope_continuation : cont;
  scope_history : list namespace_event
}.

Definition child_scope_arguments scope : ChildArguments :=
  {|child_input:=scope_input scope;child_output:=scope_output scope;child_errors:=scope_errors scope;
    child_peer_pointer:=Vptr (storage_peer (scope_storage scope)) Ptrofs.zero;
    child_pid_pointer:=Vptr (storage_pid (scope_storage scope)) Ptrofs.zero|}.

Definition child_scope_registers scope (le : temp_env) :=
  le!_input = Some (Vint (scope_input scope)) /\
  le!_output = Some (Vint (scope_output scope)) /\
  le!_errors = Some (Vint (scope_errors scope)) /\
  le!_peer = Some (Vptr (storage_peer (scope_storage scope)) Ptrofs.zero) /\
  le!_child = Some (Vptr (storage_pid (scope_storage scope)) Ptrofs.zero).

Definition child_scope_private scope :=
  ~In (storage_pair (scope_storage scope)) (handoff_borrowed_blocks (scope_borrowed scope)) /\
  ~In (storage_peer (scope_storage scope)) (handoff_borrowed_blocks (scope_borrowed scope)) /\
  ~In (storage_pid (scope_storage scope)) (handoff_borrowed_blocks (scope_borrowed scope)).

Definition child_pair_log scope first second := scope_history scope ++
  [namespace_paired (Int.repr 1) (Int.repr 524289) Int.zero
    (storage_pair (scope_storage scope)) Ptrofs.zero Int.zero first second].
Definition child_duplicate_log scope first second failure := child_pair_log scope first second ++
  [namespace_duplicated second (Int.repr 60) failure].
Definition child_closed_log scope first second failure reply := child_duplicate_log scope first second failure ++
  [namespace_process (process_entry (NativeHandoffMachine.entry_library (close_returned second reply)))].
Definition child_mask_log scope first second failure reply := child_closed_log scope first second failure reply ++
  [namespace_masked Int64.mone Int64.zero].
Definition child_signal_log scope first second failure reply := child_mask_log scope first second failure reply ++
  [namespace_defaulted (Int.repr 17) Int64.zero].
Definition child_fork_log scope first second failure reply returned := child_signal_log scope first second failure reply ++
  [namespace_forked returned].
Definition child_parent_log scope first second failure reply returned closed :=
  child_fork_log scope first second failure reply returned ++
  [namespace_process (process_entry (NativeHandoffMachine.entry_library (close_returned failure closed)))].

Definition before_local_fork event := match event with namespace_forked _|namespace_fork_lost=>False|_=>True end.
Definition child_before_fork scope log := exists suffix,
  log=scope_history scope++suffix /\ Forall before_local_fork suffix.

Lemma child_before_fork_start scope : child_before_fork scope (scope_history scope).
Proof. exists []; rewrite app_nil_r; split; [reflexivity|constructor]. Qed.

Lemma child_before_fork_extend scope log event :
  child_before_fork scope log -> before_local_fork event -> child_before_fork scope (log++[event]).
Proof.
  intros [suffix [HISTORY PREFIX]] EVENT; subst log; exists (suffix++[event]).
  split; [symmetry; apply app_assoc|].
  apply Forall_app; split; [exact PREFIX|constructor; [exact EVENT|constructor]].
Qed.

Lemma child_pair_before_fork scope first second : child_before_fork scope (child_pair_log scope first second).
Proof. apply child_before_fork_extend; [apply child_before_fork_start|exact I]. Qed.
Lemma child_duplicate_before_fork scope first second failure :
  child_before_fork scope (child_duplicate_log scope first second failure).
Proof. apply child_before_fork_extend; [apply child_pair_before_fork|exact I]. Qed.
Lemma child_closed_before_fork scope first second failure reply :
  child_before_fork scope (child_closed_log scope first second failure reply).
Proof. apply child_before_fork_extend; [apply child_duplicate_before_fork|exact I]. Qed.
Lemma child_mask_before_fork scope first second failure reply :
  child_before_fork scope (child_mask_log scope first second failure reply).
Proof. apply child_before_fork_extend; [apply child_closed_before_fork|exact I]. Qed.

Inductive ChildResult scope : list namespace_event -> Clight.state -> Prop :=
| child_setup_error_result : forall log error after,
    1 <= Int.signed error <= 4095 ->
    handoff_borrowed_input (scope_cell scope) after (scope_borrowed scope) ->
    child_before_fork scope log ->
    ChildResult scope log (Returnstate (Vint error) (call_cont (scope_continuation scope)) after)
| child_guest_result : forall first second failure reply le m,
    child_scope_registers scope le -> le!_failure = Some (Vint failure) ->
    0<=Int.signed failure ->
    handoff_borrowed_input (scope_cell scope) m (scope_borrowed scope) ->
    Mem.load Mint32 m (storage_peer (scope_storage scope)) 0 = Some (Vint first) ->
    Mem.load Mint32 m (storage_pid (scope_storage scope)) 0 = Some (Vint Int.zero) ->
    ChildResult scope (child_fork_log scope first second failure reply Int.zero)
      (Callstate (Ctypes.Internal f_guest) [Vint (scope_input scope);Vint (scope_output scope);
        Vint (scope_errors scope);Vint failure]
        (child_guest_cont (storage_pair (scope_storage scope)) le (scope_continuation scope)) m)
| child_parent_result : forall first second failure reply returned closed after,
    returned <> Int.zero -> 0<=Int.signed failure ->
    handoff_borrowed_input (scope_cell scope) after (scope_borrowed scope) ->
    Mem.load Mint32 after (storage_peer (scope_storage scope)) 0 = Some (Vint first) ->
    Mem.load Mint32 after (storage_pid (scope_storage scope)) 0 = Some (Vint returned) ->
    ChildResult scope (child_parent_log scope first second failure reply returned closed)
      (Returnstate (Vint Int.zero) (call_cont (scope_continuation scope)) after).

Ltac child_scope_registers :=
  unfold child_scope_registers in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat split; WriteAll.lookup.
