(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.evidence: Complete terminal runs exist even when close returns an error. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice Machine StoreSteps WriteAll CallPaths SourcePaths ProcessEffects ResultLayout ResultSafety
  LibraryMachine Fault SenderReportMemory ReceiverSource ReceiverReadSource ReceiverReadMemory
  ReceiverPreparation ReceiverChoice ReceiverMemory ReceiverConstruction ReceiverClassification
  ReceiverInput ReceiverCloseMemory ReceiverCloseSource ReceiverReadRuns ReceiverReadStep ReceiverTrace.
Import ListNotations.
Open Scope Z_scope.
Definition receiver_close_observed fd reply waits events := exists before rest,
  events=before++repeat library_wait waits++close_returned fd reply::rest.
Lemma receiver_close_observed_prepend : forall fd reply waits events prefix,
  receiver_close_observed fd reply waits events -> receiver_close_observed fd reply waits(prefix++events).
Proof.
  intros fd reply waits events prefix[before[rest EQ]];subst events.
  exists(prefix++before),rest;rewrite app_assoc;reflexivity.
Qed.
Lemma receiver_close_waits : forall cell fd k m waits,
  tls_ready cell m -> library_steps result_ge cell(live(Callstate close_definition[Vint fd]k m))
    (repeat library_wait waits)(live(Callstate close_definition[Vint fd]k m)).
Proof.
  intros cell fd k m waits READY;induction waits;cbn;[constructor|].
  econstructor;[apply library_wait_step;apply close_ready;exact READY|exact IHwaits].
Qed.
Theorem receiver_terminal_run : forall cell base b bytes fd bad entered done status le m output ofs run uid reply waits,
  receiver_input cell base output ofs run uid -> receiver_live_memory cell base b output ofs fd m ->
  receiver_buffer cell b m bytes ->
  le!__res=Some(Vptr output(Ptrofs.repr ofs)) ->
  le!_bad=Some(Vint bad) -> le!_entered=Some(Vint entered) ->
  le!_leader_done=Some(Vint done) -> le!_leader_status=Some(Vint status) ->
  le!_used=Some(Vlong(Int64.repr(Z.of_nat(length bytes)))) ->
  exists events final,
    library_steps result_ge cell(live(receiver_closed_state b le Kstop m))events
      (live(Returnstate Vundef Kstop final)) /\ receiver_read_trace events=[] /\
    receiver_close_observed fd reply waits events /\
    receiver_choice_result output ofs(receiver_select bytes bad entered done status)uid run b Vundef final.
Proof.
  intros cell base b bytes fd bad entered done status le m output ofs run uid reply waits
    INPUT LIVE BUFFER OUT BAD ENTERED DONE STATUS USED.
  pose proof(proj1(proj2 INPUT))as TLS.
  pose proof LIVE as[OLD[SLOTS[DEST FD]]].
  assert(VALID : Mem.valid_block base output).
  { eapply Mem.perm_valid_block with(ofs:=ofs);apply(proj2(proj2(proj2(proj1 INPUT))));lia. }
  destruct(receiver_to_close b le Kstop m fd FD)as[first PREFIX].
  destruct(close_progress cell m reply(proj1(proj2 BUFFER)))as[after EFFECT].
  pose proof(receiver_live_close _ _ _ _ _ _ _ _ _ TLS LIVE EFFECT)as LIVE'.
  pose proof(receiver_buffer_close _ _ _ _ _ _ BUFFER EFFECT)as BUFFER'.
  assert(PA : receiver_preserved cell base output ofs after).
  { apply receiver_sender_preserved;exact(proj1 LIVE'). }
  assert(SOURCE : source_returns result_ge(receiver_preserved cell base output ofs)
    (receiver_choice_result output ofs(receiver_select bytes bad entered done status)uid run b)
    (Returnstate(Vint(close_value reply))(receiver_close_cont b(PTree.set _t'25(Vint fd)le)Kstop)after)).
  { eapply source_returns_path.
    - eapply store_path_consequence;[apply receiver_close_ignored|intros last SAME;change(last=after)in SAME;subst last;exact PA].
    - eapply receiver_classification_source.
      + exact PA.
      + exact(proj1(proj2 LIVE')).
      + eapply receiver_live_result_input;[exact INPUT|exact LIVE'].
      + exact VALID.
      + exact BUFFER'.
      + WriteAll.lookup.
      + WriteAll.lookup.
      + WriteAll.lookup.
      + WriteAll.lookup.
      + WriteAll.lookup.
      + WriteAll.lookup. }
  destruct SOURCE as[last[value[final[SUFFIX POST]]]].
  destruct POST as[VALUE POST];subst value.
  exists(map original_event(repeat(source_step E0)first)++repeat library_wait waits++
    close_returned fd reply::map original_event(repeat(source_step E0)last)),final.
  split.
  - eapply library_steps_trans;[eapply receiver_source_run;exact PREFIX|].
    eapply library_steps_trans;[apply receiver_close_waits;exact(proj1(proj2 BUFFER))|].
    eapply library_steps_cons;[apply close_step;exact EFFECT|eapply receiver_source_run;exact SUFFIX].
  - split.
    + rewrite !receiver_read_trace_app,receiver_read_trace_source,receiver_read_trace_wait.
      cbn [receiver_read_trace receiver_event_bytes flat_map app];apply receiver_read_trace_source.
    + split.
      * exists(map original_event(repeat(source_step E0)first)),(map original_event(repeat(source_step E0)last));reflexivity.
      * split;[reflexivity|exact POST].
Qed.
