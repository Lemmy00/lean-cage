(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Every actual finite history stays in the read loop or exposes its real continuation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine ClightSteps StoreSteps Deterministic ResultLayout LibraryMachine LibraryPreservation
  ReceiverSource ReceiverReadMemory ReceiverRouting ReceiverReadReturns ReceiverReadStep.
Import ListNotations.

Definition receiver_stopped_suffix cell b original bad k P bytes start events target :=
  exists before tail stopped,
    events=before++tail /\
    library_steps result_ge cell(live start)before(live stopped) /\
    library_steps result_ge cell(live stopped)tail target /\
    receiver_at_stop cell b original bad k P(bytes++receiver_read_trace before)stopped.

Lemma receiver_trace_app : forall first second,
  receiver_read_trace(first++second)=receiver_read_trace first++receiver_read_trace second.
Proof. intros;apply flat_map_app. Qed.

Theorem receiver_read_history : forall cell b fd original bad k P bytes start events target,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P ->
  receiver_routed cell b fd original bad k P bytes start ->
  library_steps result_ge cell(live start)events target ->
  receiver_prefix cell b fd original bad k P(bytes++receiver_read_trace events)target \/
  receiver_stopped_suffix cell b original bad k P bytes start events target.
Proof.
  intros cell b fd original bad k P bytes start events target PRESERVE DESCRIPTOR ROUTED RUN.
  remember(live start)as initial eqn:INIT;revert start bytes INIT ROUTED.
  induction RUN as[initial|initial ev mid rest target STEP RUN IH];intros start bytes INIT ROUTED;subst initial.
  - left;cbn [receiver_read_trace flat_map];rewrite app_nil_r;apply receiver_prefix_live;exact ROUTED.
  - destruct(receiver_routed_step _ _ _ _ _ _ _ _ _ _ _ PRESERVE DESCRIPTOR ROUTED STEP)as[STOP|NEXT].
    + right;exists [],(ev::rest),start;split;[reflexivity|]. split;[constructor|].
      split;[econstructor;eassumption|]. cbn [receiver_read_trace flat_map];rewrite app_nil_r;exact STOP.
    + inversion NEXT as[next ROUTED'|m PM BUFFER];subst mid.
      * destruct(IH next(bytes++receiver_event_bytes ev)eq_refl ROUTED')as[FINAL|STOP].
        -- left;cbn [receiver_read_trace flat_map];rewrite app_assoc;exact FINAL.
        -- right;destruct STOP as[before[tail[stopped[ES[PRE[TAIL GOOD]]]]]].
           exists(ev::before),tail,stopped;split;[cbn;rewrite ES;reflexivity|].
           split;[econstructor;eassumption|]. split;[exact TAIL|].
           cbn [receiver_read_trace flat_map];rewrite app_assoc;exact GOOD.
      * destruct(library_dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst rest target.
        left;cbn [receiver_read_trace flat_map];rewrite app_nil_r;apply receiver_prefix_dead;assumption.
Qed.

Lemma receiver_routed_not_return : forall cell b fd original bad k P bytes value m,
  ~receiver_routed cell b fd original bad k P bytes(Returnstate value Kstop m).
Proof.
  intros cell b fd original bad k P bytes value m[last[PATH END]].
  inversion PATH;subst.
  - inversion END.
  - match goal with EDGE : edge _ _ _ |- _=>destruct EDGE as[_[REAL _]];inversion REAL end.
Qed.

Theorem receiver_return_reaches_stop : forall cell b fd original bad k P bytes start events value m,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P ->
  receiver_routed cell b fd original bad k P bytes start ->
  library_steps result_ge cell(live start)events(live(Returnstate value Kstop m)) ->
  receiver_stopped_suffix cell b original bad k P bytes start events(live(Returnstate value Kstop m)).
Proof.
  intros cell b fd original bad k P bytes start events value m PRESERVE DESCRIPTOR ROUTED RUN.
  destruct(receiver_read_history _ _ _ _ _ _ _ _ _ _ _ PRESERVE DESCRIPTOR ROUTED RUN)as[PREFIX|STOP];[|exact STOP].
  inversion PREFIX;subst;exfalso;eapply receiver_routed_not_return;eassumption.
Qed.

Theorem receiver_read_prefix_bound : forall cell b fd original bad k P bytes start events target,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P ->
  receiver_routed cell b fd original bad k P bytes start ->
  library_steps result_ge cell(live start)events target ->
  (length(bytes++receiver_read_trace events)<=9)%nat \/
  receiver_stopped_suffix cell b original bad k P bytes start events target.
Proof.
  intros cell b fd original bad k P bytes start events target PRESERVE DESCRIPTOR ROUTED RUN.
  destruct(receiver_read_history _ _ _ _ _ _ _ _ _ _ _ PRESERVE DESCRIPTOR ROUTED RUN)as[PREFIX|STOP];[left|right;exact STOP].
  exact(proj1(proj2(receiver_prefix_facts _ _ _ _ _ _ _ _ _ PREFIX))).
Qed.
