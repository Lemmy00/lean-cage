(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.failure: Exact stored setup fields from each completed read trace. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Machine LibraryMachine ResultLayout FrameBytes ReceiverSource ReceiverReadStep ReceiverRouting
  ReceiverInput ReceiverChoice ReceiverConstruction ReceiverOutcomes ReceiverBounds.
Open Scope Z_scope.
Theorem wire_receiver_setup_contents : forall cell base output ofs fd bad entered done status run uid events value after,
  receiver_input cell base output ofs run uid ->
  library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events
    (live(Returnstate value Kstop after)) -> Mem.load Mint32 after output ofs=Some(Vint Int.one) ->
  result_contents after output ofs Int.one(word32_at(receiver_read_trace events)0)
    (word32_at(receiver_read_trace events)4)Int.zero uid run.
Proof.
  intros cell base output ofs fd bad entered done status run uid events value after INPUT RUN KIND.
  destruct(receiver_return_trace_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)
    as[b[allocated[reason[ALLOC[STOP[VALUE[CONTENT FREED]]]]]]].
  assert(TAG : rc_kind(receiver_select(receiver_read_trace events)(receiver_bad bad reason)entered done status)=Int.one).
  { pose proof(CONTENT(cell32 0(rc_kind(receiver_select(receiver_read_trace events)(receiver_bad bad reason)entered done status)))
      ltac:(left;reflexivity))as ACTUAL.
    change(Mem.load Mint32 after output(ofs+0)=Some(Vint(rc_kind(receiver_select(receiver_read_trace events)
      (receiver_bad bad reason)entered done status))))in ACTUAL.
    rewrite Z.add_0_r in ACTUAL;congruence. }
  apply receiver_setup_kind in TAG;apply receiver_setup_exact in TAG.
  unfold receiver_select in CONTENT;rewrite TAG in CONTENT;exact CONTENT.
Qed.
