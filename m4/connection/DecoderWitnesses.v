(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.evidence: Accepted and rejected frames execute the complete actual decoder. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Library LibraryMachine LibraryControl ResultLayout ResultSafety FreshMemory
  DecoderLayout DecoderSource DecoderValidity DecoderInput DecoderProgram
  DecoderRuns DecoderAllocation.
Import ListNotations.
Open Scope Z_scope.
Definition sample_frame first kind stage detail entry elapsed :=
  map (fun i => Byte.repr
    (if Nat.eqb i 0 then first else if Nat.eqb i 1 then 67 else if Nat.eqb i 2 then 51
     else if Nat.eqb i 3 then 82 else if Nat.eqb i 4 then 1 else if Nat.eqb i 6 then kind
     else if Nat.eqb i 24 then 128 else if Nat.eqb i 32 then stage else if Nat.eqb i 36 then detail
     else if Nat.eqb i 40 then entry else if Nat.eqb i 88 then elapsed else 0)) (seq 0 160).
Theorem sample_frame_length : forall first kind stage detail entry elapsed,
  length (sample_frame first kind stage detail entry elapsed)=160%nat.
Proof. intros;unfold sample_frame;rewrite map_length,seq_length;reflexivity. Qed.
Definition accepted_frames := [sample_frame 76 0 0 0 1 0;sample_frame 76 1 1 1 0 0;
  sample_frame 76 2 0 1 1 0;sample_frame 76 4 9 1 0 0;sample_frame 76 5 0 0 0 1;
  sample_frame 76 6 8 0 1 0;sample_frame 76 7 0 0 0 0].
Theorem all_accepted_tag_samples : Forall (fun bytes => length bytes=160%nat /\
  header_valid bytes Int64.zero Int64.zero=true /\
  decoder_accepts bytes Int64.zero Int.zero Int.one Int64.zero=true) accepted_frames.
Proof.
  unfold accepted_frames.
  repeat (apply Forall_cons; [split;[apply sample_frame_length|split;vm_compute;reflexivity]|]).
  apply Forall_nil.
Qed.
Theorem every_accepted_tag_executes : forall cell bytes,
  In bytes accepted_frames -> exists base p output events after,
  decoder_input base p bytes output 0 Int64.zero Int.zero Int.one /\
  library_steps result_ge cell (live (decoder_initial p Int64.zero output 0 Kstop base)) events
    (live (Returnstate (Vint Int.zero) Kstop after)) /\
  Forall control_progress events /\ decoded_contents after output 0 bytes.
Proof.
  intros cell bytes IN.
  pose proof all_accepted_tag_samples as ALL;rewrite Forall_forall in ALL.
  destruct (ALL bytes IN) as [LEN [HEADER ACCEPT]].
  destruct (arbitrary_decoder_source_input bytes Int64.zero Int.zero Int.one LEN) as [base [p [output INPUT]]].
  destruct (decoder_finite_return_exists cell base p bytes output 0 Int64.zero Int.zero Int.one Int64.zero INPUT)
    as [events [value [after [RUN [PROGRESS [VALUE [CONTENTS REST]]]]]]].
  rewrite ACCEPT in VALUE;subst value. exists base,p,output,events,after;split;[exact INPUT|]. split;[exact RUN|]. split;[exact PROGRESS|auto].
Qed.
Definition early_rejected_frame := sample_frame 0 0 0 0 1 0.
Definition late_rejected_frame := sample_frame 76 0 0 0 3 0.
Theorem rejection_samples_exact :
  header_valid early_rejected_frame Int64.zero Int64.zero=false /\
  decoder_accepts early_rejected_frame Int64.zero Int.zero Int.one Int64.zero=false /\
  header_valid late_rejected_frame Int64.zero Int64.zero=true /\
  decoder_accepts late_rejected_frame Int64.zero Int.zero Int.one Int64.zero=false.
Proof. vm_compute;repeat constructor. Qed.
Theorem early_rejection_executes_without_output_write : forall cell,
  exists base p output events after,
  decoder_input base p early_rejected_frame output 0 Int64.zero Int.zero Int.one /\
  library_steps result_ge cell (live (decoder_initial p Int64.zero output 0 Kstop base)) events
    (live (Returnstate (Vint Int.mone) Kstop after)) /\
  Forall control_progress events /\ old_memory base after.
Proof.
  intros cell. destruct rejection_samples_exact as [HEADER [ACCEPT _]].
  destruct (arbitrary_decoder_source_input early_rejected_frame Int64.zero Int.zero Int.one
    (sample_frame_length _ _ _ _ _ _)) as [base [p [output INPUT]]].
  destruct (decoder_finite_return_exists cell base p early_rejected_frame output 0 Int64.zero Int.zero Int.one Int64.zero INPUT)
    as [events [value [after [RUN [PROGRESS [VALUE [_ [OLD REST]]]]]]]].
  rewrite ACCEPT in VALUE;subst value. exists base,p,output,events,after;split;[exact INPUT|]. split;[exact RUN|]. split;[exact PROGRESS|auto].
Qed.
Theorem late_rejection_executes_after_output_write : forall cell,
  exists base p output events after,
  decoder_input base p late_rejected_frame output 0 Int64.zero Int.zero Int.one /\
  library_steps result_ge cell (live (decoder_initial p Int64.zero output 0 Kstop base)) events
    (live (Returnstate (Vint Int.mone) Kstop after)) /\
  Forall control_progress events /\ decoded_contents after output 0 late_rejected_frame.
Proof.
  intros cell. destruct rejection_samples_exact as [_ [_ [HEADER ACCEPT]]].
  destruct (arbitrary_decoder_source_input late_rejected_frame Int64.zero Int.zero Int.one
    (sample_frame_length _ _ _ _ _ _)) as [base [p [output INPUT]]].
  destruct (decoder_finite_return_exists cell base p late_rejected_frame output 0 Int64.zero Int.zero Int.one Int64.zero INPUT)
    as [events [value [after [RUN [PROGRESS [VALUE [CONTENTS REST]]]]]]].
  rewrite ACCEPT in VALUE;subst value. exists base,p,output,events,after;split;[exact INPUT|]. split;[exact RUN|]. split;[exact PROGRESS|auto].
Qed.
