(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.evidence: Actual failed-read and TLS-address executions retain bytes and input controls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll LibraryMachine LibraryPreservation Fault ResultLayout
  ProcessEffects ReceiverSource ReceiverReadSource ReceiverReadMemory ReceiverRouting
  ReceiverReadStep ReceiverReadReturns ReceiverReadRuns ReceiverTrace.
Import ListNotations.
Open Scope Z_scope.
Definition receiver_error_observed error events := exists q,
  In(original_event(io_step q(failure error)))events.
Lemma receiver_error_observed_append : forall error events rest,
  receiver_error_observed error events -> receiver_error_observed error(events++rest).
Proof. intros error events rest[q IN];exists q;apply in_or_app;left;exact IN. Qed.
Lemma receiver_error_observed_prepend : forall error events prefix,
  receiver_error_observed error events -> receiver_error_observed error(prefix++events).
Proof. intros error events prefix[q IN];exists q;apply in_or_app;right;exact IN. Qed.
Definition receiver_error_bytes ev := match ev with
  |original_event(io_step q(failure error))=>[error]|_=>[] end.
Definition receiver_error_trace events:=flat_map receiver_error_bytes events.
Lemma receiver_error_trace_app : forall first rest,
  receiver_error_trace(first++rest)=receiver_error_trace first++receiver_error_trace rest.
Proof. intros;apply flat_map_app. Qed.
Lemma receiver_error_trace_source : forall n,
  receiver_error_trace(map original_event(repeat(source_step E0)n))=[].
Proof. induction n;cbn;auto. Qed.
Definition receiver_failed_temps le fd error :=
  receiver_saved(PTree.set _t'27(Vint fd)le)(failure error).
Theorem receiver_error_address_run : forall cell b fd original bad P bytes le m error,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P -> P m ->
  receiver_buffer cell b m bytes -> receiver_registers original bad bytes le ->(length bytes<9)%nat ->
  exists events after,
    library_steps result_ge cell(live(receiver_loop_state b le Kstop m))events
      (live(Returnstate(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))
        (receiver_errno_cont b(receiver_failed_temps le fd error)Kstop)after)) /\
    receiver_read_trace events=[] /\ receiver_error_trace events=[error] /\ P after /\
    receiver_buffer cell b after bytes /\ receiver_registers original bad bytes(receiver_failed_temps le fd error) /\
    (receiver_failed_temps le fd error)!_n=Some(Vlong Int64.mone) /\
    Mem.loadv Mint32 after(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))=Some(Vint error).
Proof.
  intros cell b fd original bad P bytes le m error PRESERVE DESCRIPTOR PM BUFFER [KEEP[BAD USED]] SHORT.
  pose proof(receiver_read_owned cell b fd m bytes BUFFER SHORT)as OWN.
  destruct(error_return_exists(receiver_request b cell fd(Z.of_nat(length bytes)))m error OWN)as[after EFFECT].
  pose proof(PRESERVE _ _ _ _ PM BUFFER SHORT EFFECT)as PA.
  pose proof(receiver_buffer_reply _ _ _ _ _ _ _ BUFFER EFFECT)as BUFFER'.
  cbn [receiver_reply_bytes]in BUFFER';rewrite app_nil_r in BUFFER'.
  destruct(receiver_loop_to_read b cell fd(Z.of_nat(length bytes))le Kstop m USED(DESCRIPTOR _ PM)ltac:(lia))as[first PREFIX].
  destruct(receiver_read_to_errno b(PTree.set _t'27(Vint fd)le)Kstop after error)as[last SUFFIX].
  exists(map original_event(repeat(source_step E0)first)++
    original_event(io_step(receiver_request b cell fd(Z.of_nat(length bytes)))(failure error))::
    map original_event(repeat(source_step E0)last)++[original_event errno_step]),after.
  split.
  - eapply library_steps_trans;[eapply receiver_source_run;exact PREFIX|].
    eapply library_steps_cons;[apply original_step|].
    + eapply Machine.effect with(q:=receiver_request b cell fd(Z.of_nat(length bytes)));
        [constructor;reflexivity|exact EFFECT].
    + eapply library_steps_trans;[eapply receiver_source_run;exact SUFFIX|].
      eapply library_steps_cons;[apply original_step;apply Machine.errno_address|constructor].
      all:destruct(proj1(proj2 BUFFER'))as[LOW[HIGH ACCESS]];assumption.
  - split.
    + rewrite receiver_read_trace_app,receiver_read_trace_source.
      change(receiver_read_trace(map original_event(repeat(source_step E0)last)++[original_event errno_step])=[]).
      rewrite receiver_read_trace_app,receiver_read_trace_source;reflexivity.
    + split.
      * rewrite receiver_error_trace_app,receiver_error_trace_source.
        change(error::receiver_error_trace(map original_event(repeat(source_step E0)last)++[original_event errno_step])=[error]).
        rewrite receiver_error_trace_app,receiver_error_trace_source;reflexivity.
      * split;[exact PA|]. split;[exact BUFFER'|]. split.
        -- split.
           ++ eapply receiver_kept_trans;[exact KEEP|]. unfold receiver_failed_temps,receiver_saved;receiver_keep.
           ++ split;unfold receiver_failed_temps,receiver_saved;WriteAll.lookup.
        -- split;[unfold receiver_failed_temps,receiver_saved;WriteAll.lookup|].
           eapply(errno_loadv(receiver_request b cell fd(Z.of_nat(length bytes))));[eapply receiver_read_owned;[exact BUFFER'|exact SHORT]|].
           exact(failure_errno _ _ _ _ EFFECT).
Qed.
