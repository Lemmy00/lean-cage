(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.values: Actual copied fork memory supplies both original caller inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine ProcessEffects ArgumentsImport.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput NativeHandoffWire NativeValues.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceMemory
  NamespaceChildResult NamespaceForkPrefix NamespaceFork NamespaceBorrow.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Local Opaque namespace_ge handoff_ge handoff_symbol.

Lemma actual_common_fork_inputs scope first second failure reply le before:
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  child_scope_registers scope le /\le!_failure=Some(Vint failure) /\0<=Int.signed failure /\
    child_storage_separate(scope_cell scope)(scope_storage scope) /\child_scope_private scope /\
    child_storage(scope_cell scope)(scope_storage scope)before /\
    handoff_borrowed_input(scope_cell scope)before(scope_borrowed scope) /\
    Mem.load Mint32 before(storage_peer(scope_storage scope))0=Some(Vint first).
Proof.
  intro FRONTIER;inversion FRONTIER;subst;try discriminate.
  match goal with SAME:child_signal_log _ _ _ _ _=child_signal_log _ _ _ _ _|-_=>
    destruct(child_signal_log_injective _ _ _ _ _ _ _ _ _ SAME)as[FIRST[SECOND[FAILURE REPLY]]];subst end.
  repeat first[assumption|split].
Qed.

Theorem same_fork_parent_borrowed_inputs scope first second failure reply le before parent child:
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  NativeForkCopy(scope_cell scope)before parent child ->
  handoff_borrowed_input(scope_cell scope)parent(scope_borrowed scope) /\
    Mem.load Mint32 parent(storage_peer(scope_storage scope))0=Some(Vint first) /\
    child_scope_registers scope le /\le!_failure=Some(Vint failure) /\
    child_storage_separate(scope_cell scope)(scope_storage scope) /\child_scope_private scope.
Proof.
  intros FRONTIER COPY;destruct(actual_common_fork_inputs _ _ _ _ _ _ _ FRONTIER)
    as[REGISTERS[FAILURE[NONNEGATIVE[SEPARATE[PRIVATE[STORAGE[BORROWED PEER]]]]]]].
  destruct COPY as[PARENT CHILD READY CHILD_READY].
  split;[eapply namespace_errno_effect_preserves_borrows;eassumption|].
  split;[eapply namespace_partial_preserves_load;[exact PARENT|exact(proj1(proj2 SEPARATE))|exact PEER]|].
  auto.
Qed.

Lemma actual_worker_run_mode_requires_normal preflight:
  handoff_worker_mode_bytes preflight=map Byte.repr[114;117;110] ->preflight=Int.zero.
Proof.
  unfold handoff_worker_mode_bytes;destruct(Int.eq preflight Int.zero)eqn:NORMAL;
    [intros;apply Int.same_if_eq;exact NORMAL|discriminate].
Qed.

Theorem same_fork_normal_parent_preflight scope first second failure reply le before parent child:
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  NativeForkCopy(scope_cell scope)before parent child ->
  handoff_worker_mode_bytes(handoff_borrowed_preflight(scope_borrowed scope))=map Byte.repr[114;117;110] ->
  Mem.loadv Mint32 parent(Vptr(handoff_symbol _preflight)Ptrofs.zero)=Some(Vint Int.zero).
Proof.
  intros FRONTIER COPY MODE.
  destruct(same_fork_parent_borrowed_inputs _ _ _ _ _ _ _ _ _ FRONTIER COPY)as[BORROWED REST].
  pose proof(handoff_borrowed_preflight_load _ _ _ BORROWED)as LOAD.
  rewrite(actual_worker_run_mode_requires_normal _ MODE)in LOAD;exact LOAD.
Qed.

(* §AR-entry.caller.values: Consume the already imported ordinary worker's exact byte-mode equality. *)
Theorem strict_same_fork_normal_parent_preflight scope first second failure reply le before parent child:
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  NativeForkCopy(scope_cell scope)before parent child ->
  Lean.eq(argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight(scope_borrowed scope))))
    (argument_bytes(map Byte.repr[114;117;110])) ->
  Mem.loadv Mint32 parent(Vptr(handoff_symbol _preflight)Ptrofs.zero)=Some(Vint Int.zero).
Proof.
  intros FRONTIER COPY MODE;apply same_fork_normal_parent_preflight with
    (scope:=scope)(first:=first)(second:=second)(failure:=failure)(reply:=reply)(le:=le)(before:=before)(child:=child);
    [exact FRONTIER|exact COPY|].
  unfold handoff_worker_mode_bytes in MODE|-*.
  destruct(Int.eq(handoff_borrowed_preflight(scope_borrowed scope))Int.zero);[reflexivity|].
  assert(SAME:argument_bytes(map Byte.repr[99;104;101;99;107])=argument_bytes(map Byte.repr[114;117;110])).
  { destruct MODE;reflexivity. }
  discriminate SAME.
Qed.

Theorem actual_common_fork_continuation scope first second failure reply k memory:
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]k memory) ->
  exists le,k=child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope).
Proof. intro FRONTIER;inversion FRONTIER;subst;try discriminate;eexists;reflexivity. Qed.
