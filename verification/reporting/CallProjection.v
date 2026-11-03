(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-reporting.interface: Actual source bytes and return/loss states refine the call interface. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Clight.
From LeanImport Require Import Lean.
Require Import NormalizedImport ReportingImport BridgeNat BridgeBytes FrameEquality
 Machine LibraryMachine ReportingTrace FrameRecord SenderSource SenderProgram SenderOutcomes SenderWriteReturn.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Lemma frame_header_named header entry cleanup fields :
 LeanCage_Reporting_Frame_badHeader(LeanCage_Reporting_Frame_mk header entry cleanup fields)=header.
Proof. reflexivity. Qed.
Lemma frame_entry_named header entry cleanup fields :
 LeanCage_Reporting_Frame_entry(LeanCage_Reporting_Frame_mk header entry cleanup fields)=entry.
Proof. reflexivity. Qed.
Lemma frame_cleanup_named header entry cleanup fields :
 LeanCage_Reporting_Frame_cleanup(LeanCage_Reporting_Frame_mk header entry cleanup fields)=cleanup.
Proof. reflexivity. Qed.
Lemma frame_fields_named header entry cleanup fields :
 LeanCage_Reporting_Frame_fields(LeanCage_Reporting_Frame_mk header entry cleanup fields)=fields.
Proof. reflexivity. Qed.

Lemma imported_append_tail A (first rest : list A) :
 List_append_inst1 A (imported_list first) (imported_list rest) = imported_list (first++rest).
Proof.
 induction first as[|x xs IH];[reflexivity|].
 change (List_cons_inst1 A x (List_append_inst1 A (imported_list xs) (imported_list rest)) =
   List_cons_inst1 A x (imported_list (xs++rest))).
 rewrite IH;reflexivity.
Qed.
Lemma imported_append_bytes first rest :
 LeanCage_Reporting_appendBytes (imported_bytes first) (imported_list(List.map imported_byte rest)) =
 imported_bytes(first++rest).
Proof.
 unfold LeanCage_Reporting_appendBytes,imported_bytes.
 change (ByteArray_mk(Array_mk_inst1 UInt8
   (List_append_inst1 UInt8(imported_list(List.map imported_byte first))(imported_list(List.map imported_byte rest)))) = ByteArray_mk(Array_mk_inst1 UInt8(imported_list(List.map imported_byte(first++rest))))).
 rewrite imported_append_tail,List.map_app;reflexivity.
Qed.

Definition source_status target := match target with
| dead _ => LeanCage_Reporting_Status_lost
| live(Returnstate value Kstop _) =>
  if Val.eq value (Vint Int.zero) then LeanCage_Reporting_Status_published else LeanCage_Reporting_Status_failed
| _ => LeanCage_Reporting_Status_running
end.
Lemma status_lost_named memory : source_status(dead memory)=LeanCage_Reporting_Status_lost.
Proof. reflexivity. Qed.

Lemma source_status_published target : source_status target=LeanCage_Reporting_Status_published ->
 exists after,target=live(Returnstate(Vint Int.zero)Kstop after).
Proof.
 destruct target as[s|m];[|discriminate].
 destruct s as[f stmt k env temps m|callee args k m|value k m];try discriminate.
 destruct k;try discriminate.
 cbn [source_status];destruct(Val.eq value (Vint Int.zero));[subst;intros;exists m;reflexivity|discriminate].
Qed.

Theorem source_call_interface cell base sequence input ofs r digest mode mode_bytes locations events target rest :
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 library_steps ResultLayout.result_ge cell (live(sender_initial Int.one sequence input ofs Kstop base)) events target ->
 outgoing_frame sequence r digest = reporting_trace events ++ rest ->
 LeanCage_Reporting_Call (imported_bytes(outgoing_frame sequence r digest))
   (imported_bytes(reporting_trace events)) (imported_list(List.map imported_byte rest)) (source_status target).
Proof.
 intros INPUT RUN PREFIX.
 unfold LeanCage_Reporting_Call;apply And_intro.
 - rewrite imported_append_bytes,<-PREFIX;constructor.
 - intro STATUS;apply imported_equality_standard in STATUS.
   destruct(source_status_published target STATUS)as[after EQ];subst target.
   destruct(sender_all_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)as[_ [[VALUE BYTES]|[VALUE FAILED]]];[|discriminate].
   rewrite standard_descriptor_frame in BYTES.
   assert(EMPTY : rest=[]).
   { rewrite BYTES in PREFIX. apply app_inv_head with (l:=outgoing_frame sequence r digest).
     rewrite app_nil_r;symmetry;exact PREFIX. }
   rewrite EMPTY;constructor.
Qed.
