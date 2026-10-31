(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Compose unbounded read retries with independently proved terminal processing. *)
From Coq Require Import List.
From compcert Require Import Values Memory Events Clight.
Require Import Machine ClightSteps StoreSteps Deterministic ResultLayout LibraryMachine LibraryControl
  CallProgress SourceGuarantees ReceiverSource ReceiverReadMemory ReceiverReadControl
  ReceiverRouting ReceiverReadReturns ReceiverReadStep ReceiverReadHistory.
Import ListNotations.

Theorem receiver_routed_progress : forall cell b fd original bad k P bytes s,
  receiver_routed cell b fd original bad k P bytes s ->
  exists ev target,control_progress ev /\ library_step result_ge cell(live s)ev target.
Proof.
  intros cell b fd original bad k P bytes s[last[PATH END]];inversion PATH;subst.
  - inversion END;subst.
    + apply receiver_read_ordinary;eapply receiver_read_owned;eassumption.
    + apply receiver_errno_ordinary;match goal with BUFFER : receiver_buffer _ _ _ _ |- _=>exact(proj1(proj2 BUFFER))end.
    + unfold receiver_closed_state,receiver_after_loop;cbn [SenderSource.statement_drop].
      exists(original_event(source_step E0));eexists;split.
      * unfold control_progress;cbn;repeat split;discriminate.
      * apply original_step;apply Machine.internal;[exact I|apply step_seq].
  - match goal with EDGE : edge _ _ _ |- _=>destruct EDGE as[IN[REAL _]]end.
    exists(original_event(source_step E0));eexists;split.
    + unfold control_progress;cbn;repeat split;discriminate.
    + apply original_step;eapply Machine.internal;[exact IN|exact REAL].
Qed.

Theorem receiver_read_continuation_guarantee : forall cell b fd original bad k P R bytes s,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P ->
  receiver_routed cell b fd original bad k P bytes s ->
  (forall received stopped,receiver_at_stop cell b original bad k P received stopped ->
    procedure_guarantee result_ge cell P R stopped) ->
  procedure_guarantee result_ge cell P R s.
Proof.
  intros cell b fd original bad k P R bytes s PRESERVE DESCRIPTOR ROUTED CONTINUE;split.
  - intros events target RUN.
    destruct(receiver_read_history _ _ _ _ _ _ _ _ _ _ _ PRESERVE DESCRIPTOR ROUTED RUN)as[PREFIX|STOP].
    + exact(proj1(receiver_prefix_facts _ _ _ _ _ _ _ _ _ PREFIX)).
    + destruct STOP as[before[tail[stopped[ES[PRE[TAIL GOOD]]]]]].
      exact(proj1(CONTINUE _ _ GOOD)_ _ TAIL).
  - intros events current RUN.
    destruct(receiver_read_history _ _ _ _ _ _ _ _ _ _ _ PRESERVE DESCRIPTOR ROUTED RUN)as[PREFIX|STOP].
    + right;inversion PREFIX;subst;eapply receiver_routed_progress;eassumption.
    + destruct STOP as[before[tail[stopped[ES[PRE[TAIL GOOD]]]]]].
      exact(proj2(CONTINUE _ _ GOOD)_ _ TAIL).
Qed.

Theorem receiver_read_continuation_weaken : forall cell b fd original bad k P Q R bytes s,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P ->
  (forall m,P m->Q m) ->
  receiver_routed cell b fd original bad k P bytes s ->
  (forall received stopped,receiver_at_stop cell b original bad k P received stopped ->
    procedure_guarantee result_ge cell Q R stopped) ->
  procedure_guarantee result_ge cell Q R s.
Proof.
  intros cell b fd original bad k P Q R bytes s PRESERVE DESCRIPTOR WEAKEN ROUTED CONTINUE;split.
  - intros events target RUN.
    destruct(receiver_read_history _ _ _ _ _ _ _ _ _ _ _ PRESERVE DESCRIPTOR ROUTED RUN)as[PREFIX|STOP].
    + apply WEAKEN;exact(proj1(receiver_prefix_facts _ _ _ _ _ _ _ _ _ PREFIX)).
    + destruct STOP as[before[tail[stopped[ES[PRE[TAIL GOOD]]]]]].
      exact(proj1(CONTINUE _ _ GOOD)_ _ TAIL).
  - intros events current RUN.
    destruct(receiver_read_history _ _ _ _ _ _ _ _ _ _ _ PRESERVE DESCRIPTOR ROUTED RUN)as[PREFIX|STOP].
    + right;inversion PREFIX;subst;eapply receiver_routed_progress;eassumption.
    + destruct STOP as[before[tail[stopped[ES[PRE[TAIL GOOD]]]]]].
      exact(proj2(CONTINUE _ _ GOOD)_ _ TAIL).
Qed.
