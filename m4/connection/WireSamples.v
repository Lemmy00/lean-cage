(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.evidence: Source pairs cover private controls, raw kind aliasing and denied payloads. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Library LibraryWitnesses LibraryMachine ResultLayout ReportingTrace FrameRecord
  SenderGlobals SenderWitnesses SenderSource SenderProgram DecoderSource DecoderInput
  WireValidity WireSource WireRuns.
Import ListNotations.
Open Scope Z_scope.
Definition wire_sample_record kind stage detail entry elapsed export_state : frame_result :=
  {|fr_kind:=Int.repr kind;fr_stage:=Int.repr stage;fr_detail:=Int.repr detail;fr_entry:=Int.repr entry;
    fr_clean:=Int.zero;fr_triggers:=Int.zero;fr_uid:=Int.repr 100000;fr_run:=Int64.one;
    fr_cpu:=Int64.zero;fr_peak:=Int64.zero;fr_out:=Int64.zero;fr_err:=Int64.zero;fr_elapsed:=Int64.repr elapsed;
    fr_oom:=Int64.zero;fr_pids:=Int64.zero;fr_export_state:=Int.repr export_state;
    fr_omitted:=Int.zero;fr_export_error:=Int.zero|}.
Definition wire_samples : list(frame_result*bool) :=
  [(wire_sample_record 0 0 42 1 0 0,true);
   (wire_sample_record 1 8 13 0 0 0,true);
   (wire_sample_record 2 0 9 1 0 0,true);
   (wire_sample_record 4 9 71 2 0 0,true);
   (wire_sample_record 5 0 0 0 1 0,true);
   (wire_sample_record 6 8 0 1 0 0,true);
   (wire_sample_record 256 0 42 1 0 0,true);
   (wire_sample_record 2 0 65 1 0 0,false);
   (wire_sample_record 3 0 0 1 0 0,false);
   (wire_sample_record 0 0 42 1 0 1,false)].
Theorem wire_sample_field_checks : Forall(fun sample=>
  wire_accepts Int64.zero(fst sample)(repeat Byte.zero 32)Int64.one(Int.repr 100000)Int.zero Int64.zero=snd sample)wire_samples.
Proof. unfold wire_samples;repeat(apply Forall_cons;[vm_compute;reflexivity|]);constructor. Qed.
Definition wire_sample_source_pair r (accepted : bool) :=
  exists cell sbase input mode sent sender_after dbase p output received decoder_after,
  sender_input cell sbase input 0 r(repeat Byte.zero 32)mode normal_bytes sender_literal_location /\
  library_steps result_ge cell(live(sender_initial Int.one Int64.zero input 0 Kstop sbase))sent
    (live(Returnstate(Vint Int.zero)Kstop sender_after)) /\
  reporting_trace sent=outgoing_frame Int64.zero r(repeat Byte.zero 32) /\
  decoder_input dbase p(reporting_trace sent)output 0 Int64.one(Int.repr 100000)Int.zero /\
  library_steps result_ge cell(live(decoder_initial p Int64.zero output 0 Kstop dbase))received
    (live(Returnstate(Vint(if accepted then Int.zero else Int.mone))Kstop decoder_after)).
Theorem wire_samples_complete_source_pairs : forall r accepted,
  In(r,accepted)wire_samples -> wire_sample_source_pair r accepted.
Proof.
  intros r accepted IN;pose proof wire_sample_field_checks as FACTS;rewrite Forall_forall in FACTS.
  pose proof(FACTS(r,accepted)IN)as ACCEPT;cbn [fst snd]in ACCEPT.
  destruct(wire_allocated_source_pair r(repeat Byte.zero 32)Int64.zero Int64.one(Int.repr 100000)Int.zero Int64.zero eq_refl)
    as[cell[sbase[input[mode[sent[sender_after[dbase[p[output[received[value[decoder_after[INPUT[SEND[BYTES[DINPUT[DECODE[VALUE POST]]]]]]]]]]]]]]]]]].
  rewrite ACCEPT in VALUE;subst value.
  exists cell,sbase,input,mode,sent,sender_after,dbase,p,output,received,decoder_after;auto.
Qed.
