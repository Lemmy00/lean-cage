(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Terminal processing adds no read bytes, including loss and close errors. *)
From Coq Require Import ZArith List.
From compcert Require Import Values Memory Events Clight.
Require Import Machine ClightSteps StoreSteps LibraryMachine LibraryPreservation LibraryControl CallPaths
  SourcePaths ReceiverReadStep CloseControl.
Import ListNotations.
Definition receiver_quiet ge cell start := forall events target,
  library_steps ge cell(live start)events target -> receiver_read_trace events=[].
Lemma receiver_read_trace_app : forall first rest,
  receiver_read_trace(first++rest)=receiver_read_trace first++receiver_read_trace rest.
Proof. intros;apply flat_map_app. Qed.
Lemma receiver_read_trace_source : forall n,
  receiver_read_trace(map original_event(repeat(source_step E0)n))=[].
Proof. induction n;cbn;auto. Qed.
Lemma receiver_read_trace_wait : forall n,receiver_read_trace(repeat library_wait n)=[].
Proof. induction n;cbn;auto. Qed.
Theorem receiver_quiet_path : forall ge cell P start count last,
  store_path ge P start count last -> receiver_quiet ge cell last -> receiver_quiet ge cell start.
Proof.
  intros ge cell P start count last PATH LAST events target RUN.
  destruct(source_path_caller_prefix _ _ _ _ _ _ PATH _ _ RUN)
    as[[n[s[remaining[COUNT[ES[TARGET TAIL]]]]]]|[[n[m[BOUND[ES[TARGET GOOD]]]]]|[rest[ES AFTER]]]];subst events.
  - apply receiver_read_trace_source.
  - rewrite receiver_read_trace_app,receiver_read_trace_source;reflexivity.
  - rewrite receiver_read_trace_app,receiver_read_trace_source;exact(LAST _ _ AFTER).
Qed.
Theorem receiver_quiet_return : forall ge cell value m,receiver_quiet ge cell(Returnstate value Kstop m).
Proof.
  intros ge cell value m events target RUN;inversion RUN;subst;[reflexivity|].
  match goal with STEP : library_step _ _ _ _ _ |- _=>
    destruct(control_return_step _ _ _ _ _ _ STEP)as[EV TARGET]end;subst.
  match goal with REST : library_steps _ _(dead _) _ _ |- _=>
    destruct(library_dead_steps _ _ _ _ _ REST)as[ES EQ]end;subst;reflexivity.
Qed.
Theorem receiver_source_quiet : forall ge cell P R start,
  source_returns ge P R start -> receiver_quiet ge cell start.
Proof.
  intros ge cell P R start[count[value[after[PATH POST]]]].
  eapply receiver_quiet_path;[exact PATH|apply receiver_quiet_return].
Qed.
Theorem receiver_close_quiet : forall ge cell fd k m,
  (forall reply after,ProcessEffects.close_effect cell m reply after ->
    receiver_quiet ge cell(Returnstate(Vint(ProcessEffects.close_value reply))k after)) ->
  receiver_quiet ge cell(Callstate close_definition[Vint fd]k m).
Proof.
  intros ge cell fd k m RETURN events target RUN.
  destruct(close_run_cases _ _ _ _ _ _ _ RUN)as[[n[ES TARGET]]|[[n[ES TARGET]]|[n[reply[after[rest[EFFECT[ES TAIL]]]]]]]];subst events.
  - apply receiver_read_trace_wait.
  - rewrite receiver_read_trace_app,receiver_read_trace_wait;reflexivity.
  - rewrite receiver_read_trace_app,receiver_read_trace_wait.
    cbn [receiver_read_trace receiver_event_bytes flat_map app].
    exact(RETURN _ _ EFFECT _ _ TAIL).
Qed.
