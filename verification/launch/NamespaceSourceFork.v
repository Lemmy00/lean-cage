(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: One actual full-source fork fixes the shared journal's initial cursor. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Clight.
Require Import Machine.
From EntryProcess Require Import ProcessMachine ProcessJournal ProcessGlobalCalls.
From EntryNamespace Require Import NamespaceMachine NamespaceGrantCut.
Import ListNotations.

Theorem actual_source_fork_occurrence run ordinal returned:
  nth_error(source_events run)ordinal=Some(namespace_forked returned) ->
  exists prefix suffix continuation before parent,
    source_events run=prefix++namespace_forked returned::suffix /\ordinal=length prefix /\
    namespace_steps caller_ge(source_cell run)(source_before run)prefix
      (live(Callstate namespace_fork_definition[]continuation before)) /\
    namespace_step caller_ge(source_cell run)
      (live(Callstate namespace_fork_definition[]continuation before))(namespace_forked returned)
      (live(Returnstate(Vint returned)continuation parent)) /\
    namespace_steps caller_ge(source_cell run)
      (live(Returnstate(Vint returned)continuation parent))suffix(source_after run) /\
    nth_error(source_events run)(length prefix)=Some(namespace_forked returned) /\
    skipn(S(length prefix))(source_events run)=suffix.
Proof.
  intro SELECTED;destruct(nth_error_split _ _ SELECTED)as[prefix[suffix[EVENTS ORDINAL]]].
  destruct(namespace_steps_at_event _ _ _ _ _ _ _ _(source_executed run)EVENTS)
    as[middle[next[PREFIX[STEP SUFFIX]]]].
  inversion STEP;subst.
  exists prefix,suffix,k,before,after;split;[exact EVENTS|]. split;[reflexivity|].
  split;[exact PREFIX|]. split;[exact STEP|]. split;[exact SUFFIX|]. split.
  - exact SELECTED.
  - rewrite EVENTS,skipn_app.
    rewrite skipn_all2 by lia.
    replace(S(length prefix)-length prefix)%nat with 1%nat by lia;cbn;reflexivity.
Qed.

(* The fields are a decomposition of one recorded C execution, retaining its
   actual memory at the one fork. They are not independently chosen branches. *)
Record ActualSourceFork(run:CallerSourceRun)(returned:Integers.int):Type:={
  source_fork_common:list NamespaceMachine.namespace_event;
  source_fork_body:list NamespaceMachine.namespace_event;
  source_fork_continuation:Clight.cont;
  source_fork_before:Memory.Mem.mem;
  source_fork_parent:Memory.Mem.mem;
  source_fork_events:source_events run=source_fork_common++NamespaceMachine.namespace_forked returned::source_fork_body;
  source_fork_prefix:NamespaceMachine.namespace_steps ProcessGlobalCalls.caller_ge(source_cell run)(source_before run)
    source_fork_common(live(Callstate NamespaceMachine.namespace_fork_definition[]source_fork_continuation source_fork_before));
  source_fork_operation:NamespaceMachine.namespace_step ProcessGlobalCalls.caller_ge(source_cell run)
    (live(Callstate NamespaceMachine.namespace_fork_definition[]source_fork_continuation source_fork_before))
    (NamespaceMachine.namespace_forked returned)
    (live(Returnstate(Vint returned)source_fork_continuation source_fork_parent));
  source_fork_suffix:NamespaceMachine.namespace_steps ProcessGlobalCalls.caller_ge(source_cell run)
    (live(Returnstate(Vint returned)source_fork_continuation source_fork_parent))source_fork_body(source_after run)
}.

Theorem actual_source_fork_record run ordinal returned:
  nth_error(source_events run)ordinal=Some(namespace_forked returned) ->
  exists fork:ActualSourceFork run returned,ordinal=length(source_fork_common _ _ fork).
Proof.
  intro SELECTED;destruct(actual_source_fork_occurrence _ _ _ SELECTED)
    as[prefix[suffix[k[before[parent[EVENTS[ORDINAL[PREFIX[STEP[SUFFIX REST]]]]]]]]]].
  eexists {|source_fork_common:=prefix;source_fork_body:=suffix;source_fork_continuation:=k;
    source_fork_before:=before;source_fork_parent:=parent;source_fork_events:=EVENTS;
    source_fork_prefix:=PREFIX;source_fork_operation:=STEP;source_fork_suffix:=SUFFIX|};exact ORDINAL.
Qed.
