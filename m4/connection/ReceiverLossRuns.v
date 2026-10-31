(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.evidence: Actual partial-read loss retains transferred bytes and never becomes a result return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine StoreSteps LibraryMachine Fault ResultLayout ReceiverSource
  ReceiverReadSource ReceiverReadMemory ReceiverRouting ReceiverReadStep ReceiverInput
  ReceiverEntry ReceiverReadRuns ReceiverTrace ReceiverProgram ReceiverMemory.
Import ListNotations.
Open Scope Z_scope.
Lemma receiver_read_waits : forall cell b fd used le k m waits,
  owned(receiver_request b cell fd used)m ->
  library_steps result_ge cell(live(receiver_read_state b cell fd used le k m))
    (repeat(original_event wait_step)waits)(live(receiver_read_state b cell fd used le k m)).
Proof.
  intros cell b fd used le k m waits OWN;induction waits;cbn;[constructor|].
  econstructor;[apply original_step;eapply Machine.waiting with(q:=receiver_request b cell fd used);
    [unfold receiver_read_state;apply(at_io cell(receiver_request b cell fd used));reflexivity|exact OWN]|exact IHwaits].
Qed.
Lemma receiver_read_trace_io_wait : forall waits,
  receiver_read_trace(repeat(original_event wait_step)waits)=[].
Proof. induction waits;cbn;auto. Qed.
Theorem receiver_partial_read_loss : forall cell base output ofs fd bad entered done status run uid bytes waits,
  receiver_input cell base output ofs run uid ->0<Z.of_nat(length bytes)<=9 ->
  exists b events after,
    library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events(dead after) /\
    events=map original_event(repeat(source_step E0)(length events-waits-1))++
      repeat(original_event wait_step)waits++[original_event(partial_loss(receiver_request b cell fd 0)bytes None)] /\
    receiver_read_trace events=bytes /\ receiver_preserved cell base output ofs after.
Proof.
  intros cell base output ofs fd bad entered done status run uid bytes waits INPUT SIZE.
  destruct(receiver_entry_prepared cell base output ofs fd bad entered done status run uid INPUT)
    as[b[allocated[initialized[count[ALLOC[PATH[LIVE[BUFFER[KEEP[BAD USED]]]]]]]]]].
  pose proof(receiver_read_owned cell b fd initialized [] BUFFER ltac:(cbn;lia))as OWN.
  destruct(read_transfer_exists(receiver_request b cell fd 0)initialized bytes OWN eq_refl SIZE)as[after EFFECT].
  destruct(receiver_loop_to_read b cell fd 0(receiver_first_temps output ofs fd bad entered done status)Kstop initialized
    USED(proj2(proj2(proj2 LIVE)))ltac:(lia))as[first PREFIX].
  set(events:=map original_event(repeat(source_step E0)(count+first))++
    repeat(original_event wait_step)waits++[original_event(partial_loss(receiver_request b cell fd 0)bytes None)]).
  assert(RUN : library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events(dead after)).
  { unfold events;rewrite repeat_app,map_app,<-app_assoc.
    eapply library_steps_trans;[eapply receiver_source_run;exact PATH|].
    eapply library_steps_trans;[eapply receiver_source_run;exact PREFIX|].
    eapply library_steps_trans;[apply receiver_read_waits;exact OWN|].
    eapply library_steps_cons;[apply original_step|constructor].
    eapply Machine.lose_during_io with(q:=receiver_request b cell fd 0);
      [constructor;reflexivity|exact EFFECT]. }
  exists b,events,after;split;[exact RUN|]. split.
  - unfold events;rewrite !app_length,!map_length,!repeat_length;cbn [length].
    replace(count+first+ (waits+1)-waits-1)%nat with(count+first)%nat by lia;reflexivity.
  - split.
    + unfold events;rewrite !receiver_read_trace_app,receiver_read_trace_source,receiver_read_trace_io_wait.
      cbn [receiver_read_trace receiver_event_bytes flat_map operation receiver_request app];apply app_nil_r.
    + exact(receiver_all_prefixes cell base output ofs fd bad entered done status run uid events(dead after)INPUT RUN).
Qed.
