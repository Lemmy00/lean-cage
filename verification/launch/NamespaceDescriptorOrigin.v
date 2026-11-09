(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.receipt: The selected descriptors retain their actual common-source origin. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Clight.
From LeanImport Require Import Lean.
Require Import Machine.
From EntryProcess Require Import ProcessJournal.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespacePaths NamespaceMemory NamespaceChildResult
  NamespaceForkPrefix NamespaceForkWitness NamespaceForkInputs NamespaceSourceFork NamespaceTraceRegion NamespaceHandles.
Import ListNotations.
Local Close Scope lean_scope.

Definition SourceDescriptorOrigin run returned(fork:ActualSourceFork run returned)first failure:Prop:=
  exists(scope:ChildScope)(second:int)(reply:ProcessEffects.close_reply)(temps:temp_env),
    scope_history scope=[] /\scope_cell scope=source_cell run /\
    source_fork_continuation _ _ fork=child_fork_cont(storage_pair(scope_storage scope))temps(scope_continuation scope) /\
    namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply /\
    ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
      (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)).

Fixpoint source_created_peer(events:list namespace_event):option int:=match events with
  |[]=>None
  |namespace_paired _ _ _ _ _ _ first _::_=>Some first
  |_::rest=>source_created_peer rest end.

Fixpoint source_duplicated_failure(events:list namespace_event):option int:=match events with
  |[]=>None
  |namespace_duplicated _ _ failure::_=>Some failure
  |_::rest=>source_duplicated_failure rest end.

Lemma source_descriptor_signal_log scope first second failure reply:
  scope_history scope=[] ->
  source_created_peer(child_signal_log scope first second failure reply)=Some first /\
  source_duplicated_failure(child_signal_log scope first second failure reply)=Some failure.
Proof.
  intro HISTORY;unfold child_signal_log,child_mask_log,child_closed_log,child_duplicate_log,child_pair_log;rewrite HISTORY.
  split;reflexivity.
Qed.

Lemma source_useful_descriptor_log pair:
  source_created_peer(namespace_fd_events(repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10)))=
    Some(Int.repr 9) /\
  source_duplicated_failure(namespace_fd_events(repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10)))=
    Some(Int.repr 60).
Proof. vm_compute;split;reflexivity. Qed.

Theorem actual_useful_descriptor_origin run returned(fork:ActualSourceFork run returned)pair first failure:
  source_fork_common _ _ fork=repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10) ->
  SourceDescriptorOrigin run returned fork first failure ->first=Int.repr 9 /\failure=Int.repr 60.
Proof.
  intros COMMON[scope[second[reply[temps[HISTORY[CELL[CONT[LOG FRONTIER]]]]]]]].
  destruct(source_descriptor_signal_log scope first second failure reply HISTORY)as[PEER FAILURE].
  destruct(source_useful_descriptor_log pair)as[ACTUAL_PEER ACTUAL_FAILURE].
  rewrite <-LOG,COMMON in PEER,FAILURE;split;congruence.
Qed.

Theorem actual_failure_descriptor_nonnegative run returned(fork:ActualSourceFork run returned)first failure:
  SourceDescriptorOrigin run returned fork first failure ->(0<=Int.signed failure)%Z.
Proof.
  intros[scope[second[reply[temps[HISTORY[CELL[CONT[LOG FRONTIER]]]]]]]].
  rewrite LOG,CONT in FRONTIER.
  destruct(actual_common_fork_inputs scope first second failure reply temps(source_fork_before _ _ fork)FRONTIER)
    as[REGISTERS[DESCRIPTOR[NONNEGATIVE REST]]];exact NONNEGATIVE.
Qed.

Theorem actual_failure_descriptor_number_bound run returned(fork:ActualSourceFork run returned)first failure:
  SourceDescriptorOrigin run returned fork first failure ->
  (Z.of_nat(nat_of_Nat(native_descriptor_number failure))<=Int.max_signed)%Z.
Proof.
  intro ORIGIN.
  destruct(native_descriptor_number_valid failure(actual_failure_descriptor_nonnegative _ _ _ _ _ ORIGIN))as[BOUND EXACT].
  apply Z.leb_le;exact BOUND.
Qed.
