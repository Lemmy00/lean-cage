(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.classification: Actual SETUP output implies exact eight-byte framing and bounded decoded fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Machine LibraryMachine ResultLayout FrameBytes ReceiverSource ReceiverReadStep
  ReceiverRouting ReceiverInput ReceiverChoice ReceiverConstruction ReceiverOutcomes ReceiverBounds.
Open Scope Z_scope.
Theorem receiver_actual_setup_bounds : forall cell base output ofs fd bad entered done status run uid events value after,
  receiver_input cell base output ofs run uid ->
  library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events
    (live(Returnstate value Kstop after)) -> Mem.load Mint32 after output ofs=Some(Vint Int.one) ->
  length(receiver_read_trace events)=8%nat /\ bad=Int.zero /\ entered=Int.zero /\
    1<=Int.unsigned(word32_at(receiver_read_trace events)0)<=8 /\
    1<=Int.unsigned(word32_at(receiver_read_trace events)4)<=4095.
Proof.
  intros cell base output ofs fd bad entered done status run uid events value after INPUT RUN KIND.
  destruct(receiver_return_trace_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)
    as[b[allocated[reason[ALLOC[STOP[VALUE[CONTENT FREED]]]]]]].
  set(choice:=receiver_select(receiver_read_trace events)(receiver_bad bad reason)entered done status).
  assert(TAG : rc_kind choice=Int.one).
  { pose proof(CONTENT(cell32 0(rc_kind choice))ltac:(left;reflexivity))as ACTUAL.
    change(Mem.load Mint32 after output(ofs+0)=Some(Vint(rc_kind choice)))in ACTUAL.
    rewrite Z.add_0_r in ACTUAL;congruence. }
  destruct(receiver_setup_bounds _ _ _ _ _
    (receiver_read_nine_byte_bound _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)
    (receiver_setup_kind _ _ _ _ _ TAG))as[LEN[BAD[ENTERED[STAGE ERROR]]]].
  split;[exact LEN|]. split.
  - destruct reason;cbn in BAD;try exact BAD;discriminate BAD.
  - split;[exact ENTERED|]. split;assumption.
Qed.
