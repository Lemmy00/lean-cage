(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The consumed grant names an earlier send in the same physical history. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import ArgumentsImport.
From EntryNamespace Require Import NamespaceObjects NamespaceChannel.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Inductive checked_grant_order(sent read:nat):Prop:=
| checked_grant_order_intro:
    LeanCage_Entry_PhysicalHandoff_grantBeforeRead(Nat_of_nat sent)(Nat_of_nat read) ->
    checked_grant_order sent read.

Theorem physical_order_is_ordinary sent read:
  sent<read ->LeanCage_Entry_PhysicalHandoff_grantBeforeRead(Nat_of_nat sent)(Nat_of_nat read).
Proof.
  intro BEFORE;unfold LeanCage_Entry_PhysicalHandoff_grantBeforeRead.
  change(Nat_of_nat(S sent)<=Nat_of_nat read)%Nat.
  apply nat_le_Nat_le';exact BEFORE.
Qed.

Theorem actual_private_read_has_prior_send parent channel history before tables actor fd wanted bytes after byte:
  Forall(fun observation=>grant_write_owned(Datatypes.fst observation)parent channel(Datatypes.snd observation))history ->
  channel_execution channel channel_empty history before ->
  (exists binding,tables actor fd=Some binding /\
    descriptor_object binding=release_endpoint channel child_endpoint) ->
  channel_operation tables channel before(channel_read actor fd wanted bytes)after ->
  In byte bytes ->exists source_tables source_fd sent lost position,
    nth_error history position=Some(source_tables,channel_sent parent source_fd sent lost) /\
    In byte sent /\position<length history /\checked_grant_order position(length history).
Proof.
  intros OWNED RUN CHILD READ BYTE.
  destruct(private_read_byte_has_parent_write _ _ _ _ _ _ _ _ _ _ _ OWNED RUN CHILD READ BYTE)
    as[source_tables[source_fd[sent[lost[EARLIER SENT]]]]].
  apply In_nth_error in EARLIER as[position OBSERVED].
  assert(BEFORE:position<length history).
  { apply nth_error_Some;rewrite OBSERVED;discriminate. }
  exists source_tables,source_fd,sent,lost,position;split;[exact OBSERVED|].
  split;[exact SENT|]. split;[exact BEFORE|].
  constructor;apply physical_order_is_ordinary;exact BEFORE.
Qed.


Theorem actual_private_read_has_prior_global_send(A:Type)
    (project:A->(nat->DescriptorTable)*ChannelEvent)
    parent channel global before tables actor fd wanted bytes after byte:
  Forall(fun observation=>grant_write_owned(Datatypes.fst observation)parent channel(Datatypes.snd observation))
    (map project global) ->
  channel_execution channel channel_empty(map project global)before ->
  (exists binding,tables actor fd=Some binding /\
    descriptor_object binding=release_endpoint channel child_endpoint) ->
  channel_operation tables channel before(channel_read actor fd wanted bytes)after ->
  In byte bytes ->exists raw source_tables source_fd sent lost position,
    nth_error global position=Some raw /\
    project raw=(source_tables,channel_sent parent source_fd sent lost) /\
    In byte sent /\position<length global /\checked_grant_order position(length global).
Proof.
  intros OWNED RUN CHILD READ BYTE.
  destruct(actual_private_read_has_prior_send _ _ _ _ _ _ _ _ _ _ _ OWNED RUN CHILD READ BYTE)
    as[source_tables[source_fd[sent[lost[position[OBSERVED[SENT[BEFORE ORDER]]]]]]]].
  rewrite nth_error_map in OBSERVED.
  destruct(nth_error global position)as[raw|]eqn:RAW;[|discriminate].
  cbn in OBSERVED;inversion OBSERVED.
  exists raw,source_tables,source_fd,sent,lost,position.
  split;[exact RAW|]. split;[assumption|]. split;[exact SENT|].
  rewrite length_map in BEFORE,ORDER;split;assumption.
Qed.
