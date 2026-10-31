(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.evidence: Allocated complete-source witnesses include malformed input and ignored close failure. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import IO Machine LibraryMachine ProcessEffects ResultLayout FrameRecord ReceiverInput ReceiverChoice
  ReceiverReadStep ReceiverConstruction ReceiverTerminalRuns ReceiverWitnessInputs ReceiverFaultRuns.
Import ListNotations.
Open Scope Z_scope.
Definition receiver_example bad entered done status bytes kind stage detail entry reply waits retries :=
  exists cell base output events final,
    receiver_input cell base output 0(Int64.repr 1)(Int.repr 1000) /\
    library_steps result_ge cell(live(ReceiverSource.receiver_initial output 0(Int.repr 3)bad entered done status Kstop base))events
      (live(Returnstate Vundef Kstop final)) /\ receiver_read_trace events=bytes /\
    receiver_retries_observed retries events /\ receiver_close_observed(Int.repr 3)reply waits events /\
    result_contents final output 0 kind stage detail entry(Int.repr 1000)(Int64.repr 1).
Theorem receiver_example_exists : forall bad entered done status bytes reply waits retries,
  (length bytes<=9)%nat ->
  let choice:=receiver_select bytes bad entered done status in
  receiver_example bad entered done status bytes(rc_kind choice)(rc_stage choice)(rc_detail choice)(rc_entry choice)reply waits retries.
Proof.
  intros bad entered done status bytes reply waits retries LIMIT;cbn zeta.
  destruct(receiver_inputs_inhabited(Int64.repr 1)(Int.repr 1000))as[cell[base[output INPUT]]].
  destruct(receiver_complete_retry_run cell base output 0(Int.repr 3)bad entered done status(Int64.repr 1)(Int.repr 1000)
    bytes reply waits retries INPUT LIMIT)as[b[allocated[events[final[ALLOC[RUN[TRACE[RETRIES[CLOSE[VALUE[CONTENT FREED]]]]]]]]]]].
  exists cell,base,output,events,final;split;[exact INPUT|]. split;[exact RUN|]. split;[exact TRACE|].
  split;[exact RETRIES|]. split;[exact CLOSE|exact CONTENT].
Qed.
Example receiver_setup_actual_run : forall waits retries,
  receiver_example Int.zero Int.zero Int.one Int.zero
    (frame_word32 Int.one++frame_word32(Int.repr 13))Int.one Int.one(Int.repr 13)Int.zero
    (close_error(Int.repr 9))waits retries.
Proof. intros;eapply receiver_example_exists;vm_compute;lia. Qed.
Example receiver_short_actual_run : forall waits retries,
  receiver_example Int.zero Int.zero Int.one Int.zero(repeat Byte.zero 3)
    (Int.repr 4)(Int.repr 9)(Int.repr 71)(Int.repr 2)(close_ok None)waits retries.
Proof. intros;eapply receiver_example_exists;vm_compute;lia. Qed.
Example receiver_ninth_byte_actual_run : forall waits retries,
  receiver_example Int.zero Int.zero Int.one Int.zero
    (frame_word32 Int.one++frame_word32 Int.one++[Byte.zero])
    (Int.repr 4)(Int.repr 9)(Int.repr 71)(Int.repr 2)(close_ok None)waits retries.
Proof. intros;eapply receiver_example_exists;vm_compute;lia. Qed.
Example receiver_exit_actual_run : forall waits retries,
  receiver_example Int.zero Int.one Int.one(Int.repr 10752)[]
    Int.zero Int.zero(Int.repr 42)Int.one(close_ok None)waits retries.
Proof. intros;eapply receiver_example_exists;cbn;lia. Qed.
Example receiver_signal_actual_run : forall waits retries,
  receiver_example Int.zero Int.one Int.one(Int.repr 9)[]
    (Int.repr 2)Int.zero(Int.repr 9)Int.one(close_ok None)waits retries.
Proof. intros;eapply receiver_example_exists;cbn;lia. Qed.
Example receiver_stopped_status_actual_run : forall waits retries,
  receiver_example Int.zero Int.one Int.one(Int.repr 127)[]
    (Int.repr 4)(Int.repr 9)(Int.repr 71)Int.one(close_ok None)waits retries.
Proof. intros;eapply receiver_example_exists;cbn;lia. Qed.
Example receiver_arbitrary_signal_domain_actual_run : forall waits retries,
  receiver_example Int.zero Int.one Int.one(Int.repr 65)[]
    (Int.repr 2)Int.zero(Int.repr 65)Int.one(close_ok None)waits retries.
Proof. intros;eapply receiver_example_exists;cbn;lia. Qed.
