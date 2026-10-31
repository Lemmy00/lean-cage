(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.evidence: Useful actual read executions reach EOF or the ninth-byte stop. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll LibraryMachine LibraryPreservation Fault ResultLayout
  ReceiverSource ReceiverReadSource ReceiverReadMemory ReceiverRouting ReceiverReadStep
  ReceiverReadReturns ReceiverTrace.
Import ListNotations.
Open Scope Z_scope.
Lemma receiver_source_run : forall cell P start count last,
  store_path result_ge P start count last ->
  library_steps result_ge cell(live start)(map original_event(repeat(source_step E0)count))(live last).
Proof. intros;apply original_runs_preserved;eapply store_path_actual;exact H. Qed.
Theorem receiver_loop_stop_run : forall cell b fd original bad bytes le m,
  receiver_buffer cell b m bytes -> receiver_registers original bad bytes le ->
  Mem.load Mint32 m(rb_pipe b)0=Some(Vint fd) ->
  exists events next reason,
    library_steps result_ge cell(live(receiver_loop_state b le Kstop m))events
      (live(receiver_closed_state b next Kstop m)) /\
    receiver_read_trace events=[] /\ receiver_stop_valid reason bytes /\
    receiver_bad bad reason=bad /\ receiver_registers original bad bytes next.
Proof.
  intros cell b fd original bad bytes le m BUFFER REGS FD;pose proof REGS as[KEEP[BAD USED]].
  destruct(Nat.eq_dec(length bytes)9)as[FULL|SHORT].
  - destruct(receiver_full_to_close b le Kstop m)as[count PATH];[rewrite FULL in USED;exact USED|].
    exists(map original_event(repeat(source_step E0)count)),le,receive_full.
    split;[eapply receiver_source_run;exact PATH|]. split;[apply receiver_read_trace_source|].
    split;[exact FULL|]. split;[reflexivity|exact REGS].
  - assert(SIZE : (length bytes<9)%nat)by(pose proof(proj1 BUFFER);lia).
    destruct(receiver_loop_to_read b cell fd(Z.of_nat(length bytes))le Kstop m USED FD ltac:(lia))as[first PREFIX].
    set(readle:=PTree.set _t'27(Vint fd)le).
    assert(USED' : readle!_used=Some(Vlong(Int64.repr(Z.of_nat(length bytes)))))by(unfold readle;WriteAll.lookup).
    destruct(receiver_zero_to_close b readle Kstop m(Z.of_nat(length bytes))None USED')
      as[last[next[KEPT[BAD'[USED'' SUFFIX]]]]].
    exists(map original_event(repeat(source_step E0)first)++
      original_event(io_step(receiver_request b cell fd(Z.of_nat(length bytes)))(zero None))::
      map original_event(repeat(source_step E0)last)),next,receive_eof.
    split.
    + eapply library_steps_trans;[eapply receiver_source_run;exact PREFIX|].
      eapply library_steps_cons;[apply original_step|eapply receiver_source_run;exact SUFFIX].
      eapply Machine.effect with(q:=receiver_request b cell fd(Z.of_nat(length bytes)));
        [constructor;reflexivity|]. apply zero_returns;[eapply receiver_read_owned;eassumption|constructor].
    + split.
      * rewrite receiver_read_trace_app,receiver_read_trace_source;cbn [receiver_read_trace receiver_event_bytes flat_map app].
        apply receiver_read_trace_source.
      * split;[exact SIZE|]. split;[reflexivity|]. split.
        -- eapply receiver_kept_trans;[exact KEEP|]. eapply receiver_kept_trans;[|exact KEPT]. unfold readle;receiver_keep.
        -- split;[rewrite BAD';unfold readle;WriteAll.lookup|exact USED''].
Qed.
Theorem receiver_loop_transfer_run : forall cell b fd original bad P prefix bytes le m,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P -> P m ->
  receiver_buffer cell b m prefix -> receiver_registers original bad prefix le ->
  0<Z.of_nat(length bytes)<=9-Z.of_nat(length prefix) ->
  exists events next after,
    library_steps result_ge cell(live(receiver_loop_state b le Kstop m))events
      (live(receiver_loop_state b next Kstop after)) /\
    receiver_read_trace events=bytes /\ P after /\ receiver_buffer cell b after(prefix++bytes) /\
    receiver_registers original bad(prefix++bytes)next.
Proof.
  intros cell b fd original bad P prefix bytes le m PRESERVE DESCRIPTOR PM BUFFER [KEEP[BAD USED]] SIZE.
  assert(SHORT : (length prefix<9)%nat)by lia.
  pose proof(receiver_read_owned cell b fd m prefix BUFFER SHORT)as OWN.
  destruct(read_transfer_exists(receiver_request b cell fd(Z.of_nat(length prefix)))m bytes OWN eq_refl SIZE)
    as[after EFFECT].
  pose proof(PRESERVE _ _ _ _ PM BUFFER SHORT EFFECT)as PA.
  pose proof(receiver_buffer_transfer _ _ _ _ _ _ _ _ BUFFER EFFECT)as BUFFER'.
  destruct(receiver_loop_to_read b cell fd(Z.of_nat(length prefix))le Kstop m USED(DESCRIPTOR _ PM)ltac:(lia))as[first PREFIX].
  set(readle:=PTree.set _t'27(Vint fd)le).
  assert(USED' : readle!_used=Some(Vlong(Int64.repr(Z.of_nat(length prefix)))))by(unfold readle;WriteAll.lookup).
  destruct(receiver_positive_to_loop b readle Kstop after(Z.of_nat(length prefix))bytes None USED' ltac:(lia)SIZE)
    as[last[next[KEPT[BAD'[USED'' SUFFIX]]]]].
  exists(map original_event(repeat(source_step E0)first)++
    original_event(io_step(receiver_request b cell fd(Z.of_nat(length prefix)))(transfer bytes None))::
    map original_event(repeat(source_step E0)last)),next,after.
  split.
  - eapply library_steps_trans;[eapply receiver_source_run;exact PREFIX|].
    eapply library_steps_cons;[apply original_step|eapply receiver_source_run;exact SUFFIX].
    eapply Machine.effect with(q:=receiver_request b cell fd(Z.of_nat(length prefix)));
      [constructor;reflexivity|exact EFFECT].
  - split.
    + rewrite receiver_read_trace_app,receiver_read_trace_source.
      change(bytes++receiver_read_trace(map original_event(repeat(source_step E0)last))=bytes).
      rewrite receiver_read_trace_source,app_nil_r;reflexivity.
    + split;[exact PA|]. split;[exact BUFFER'|]. split.
      * eapply receiver_kept_trans;[exact KEEP|]. eapply receiver_kept_trans;[|exact KEPT]. unfold readle;receiver_keep.
      * split;[rewrite BAD';unfold readle;WriteAll.lookup|]. rewrite app_length,Nat2Z.inj_add;exact USED''.
Qed.
Theorem receiver_loop_feed_run : forall cell b fd original bad P bytes le m,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P -> P m ->
  receiver_buffer cell b m [] -> receiver_registers original bad [] le ->(length bytes<=9)%nat ->
  exists events next after,
    library_steps result_ge cell(live(receiver_loop_state b le Kstop m))events
      (live(receiver_loop_state b next Kstop after)) /\ receiver_read_trace events=bytes /\
    P after /\ receiver_buffer cell b after bytes /\ receiver_registers original bad bytes next.
Proof.
  intros cell b fd original bad P bytes le m PRESERVE DESCRIPTOR PM BUFFER REGS LIMIT.
  destruct bytes as[|first rest].
  - exists [],le,m;split;[constructor|]. split;[reflexivity|]. split;[exact PM|]. split;assumption.
  - eapply receiver_loop_transfer_run with(prefix:=[]);
      [exact PRESERVE|exact DESCRIPTOR|exact PM|exact BUFFER|exact REGS|cbn in *;lia].
Qed.
