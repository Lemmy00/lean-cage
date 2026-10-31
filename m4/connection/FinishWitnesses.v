(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Allocated callers witness both full publication and ignored publication failure. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Library LibraryMachine LibraryWitnesses ResultLayout ReportingTrace FrameRecord SenderSource
  SenderGlobals SenderWitnesses SenderProgram FinishSource FinishControl FinishPublication.
Import ListNotations.
Open Scope Z_scope.
Theorem allocated_finish_publication_outcomes : forall (publish : bool) r digest,
  length digest=32%nat -> exists cell base input mode events after,
    sender_input cell base input 0 r digest mode normal_bytes sender_literal_location /\
    library_steps result_ge cell (live (finish_initial input 0 Kstop base)) events
      (live (Returnstate (Vint (finish_exit_word r)) Kstop after)) /\
    finish_result base r (Vint (finish_exit_word r)) after /\
    reporting_trace events=(if publish then outgoing_frame Int64.zero r digest else []).
Proof.
  intros publish r digest LEN.
  destruct (arbitrary_sender_input r digest normal_bytes LEN
    ltac:(repeat constructor;vm_compute;discriminate) ltac:(cbn;lia)) as [cell [base [input [mode INPUT]]]].
  destruct (finish_publication_outcome_exists publish cell base input 0 r digest mode normal_bytes sender_literal_location INPUT)
    as [events [after [RUN [RESULT BYTES]]]].
  exists cell,base,input,mode,events,after;split;[exact INPUT|]. split;[exact RUN|]. split;assumption.
Qed.
