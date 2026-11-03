(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.connection: Compiler-preserved reporting consumes the existing source and decoder proof. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Smallstep Clight Asm.
From LeanCageMain Require Main.
Require Import Machine LibraryMachine ReportingTrace ResultLayout FrameRecord SenderSource
 SenderProgram SenderOutcomes SenderWriteReturn PrimitiveCalls StockCalls VerifiedBackend CompilerCalls
 NormalizedImport FrameEquality BridgeBytes ReportingImport SourceConnection RuntimeProgram.
Local Close Scope lean_scope.
Import ListNotations.
Local Opaque RuntimeProgram.program.

Section SOURCE.
Variables (cell : tls) (base : mem) (sequence : int64) (input : block) (ofs : Z)
 (r : frame_result) (digest : list Byte.int) (mode : Library.address) (mode_bytes : list Byte.int)
 (locations : SenderSelectors.report_fault -> block).
Hypothesis INPUT : sender_input cell base input ofs r digest mode mode_bytes locations.

Lemma sender_source_ready events s :
 library_steps result_ge cell(live(sender_initial Int.one sequence input ofs Kstop base))events(live s) ->
 source_ready result_ge cell s.
Proof.
 intro RUN.
 destruct(sender_defined_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)
   as[[value[after[EQ[sent RESULT]]]]|PROGRESS];[|right;exact PROGRESS].
 subst s;unfold sender_result,sender_output_result in RESULT.
 destruct RESULT as[_[[VALUE BYTES]|[VALUE FAILED]]];subst value;
   left;eexists;constructor.
Qed.

Variable observe : Events.event -> list Byte.int.
Hypothesis RUNTIME : runtime_contract result_ge cell observe
 (sender_initial Int.one sequence input ofs Kstop base).

Theorem sender_stock_run trace after :
 star Clight.step2 result_ge(sender_initial Int.one sequence input ofs Kstop base)trace after ->
 exists events,
   library_steps result_ge cell(live(sender_initial Int.one sequence input ofs Kstop base))events(live after) /\
   trace_bytes observe trace=reporting_trace events.
Proof.
 intro RUN;eapply stock_run_source;[exact RUNTIME|exact sender_source_ready|exact RUN|constructor].
Qed.

Theorem sender_stock_progress trace after :
 star Clight.step2 result_ge(sender_initial Int.one sequence input ofs Kstop base)trace after ->
 (exists value,Clight.final_state after value) \/
 (exists trace next,Clight.step2 result_ge after trace next).
Proof.
 intro RUN;destruct(sender_stock_run _ _ RUN)as[events[SOURCE BYTES]].
 eapply ready_stock_progress;[exact RUNTIME|exact SOURCE|eapply sender_source_ready;exact SOURCE].
Qed.

Theorem sender_stock_prefix trace after :
 star Clight.step2 result_ge(sender_initial Int.one sequence input ofs Kstop base)trace after ->
 exists rest,outgoing_frame sequence r digest=trace_bytes observe trace++rest.
Proof.
 intro RUN;destruct(sender_stock_run _ _ RUN)as[events[SOURCE BYTES]].
 destruct(sender_all_prefixes _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT SOURCE)as[_[rest PREFIX]].
 rewrite standard_descriptor_frame in PREFIX;exists rest;rewrite BYTES;exact PREFIX.
Qed.

Theorem sender_stock_decodes trace after :
 star Clight.step2 result_ge(sender_initial Int.one sequence input ofs Kstop base)trace
   (Returnstate(Vint Int.zero)Kstop after) ->
 LeanCageM4_Normalized_decode(imported_bytes(trace_bytes observe trace))=
   LeanCage_Reporting_decodeFrame(source_frame sequence r digest).
Proof.
 intro RUN;destruct(sender_stock_run _ _ RUN)as[events[SOURCE BYTES]].
 exact(eq_trans
   (f_equal (fun bytes=>LeanCageM4_Normalized_decode(imported_bytes bytes)) BYTES)
   (imported_equality_standard _ _ _
     (source_sender_decoder cell base sequence input ofs r digest mode mode_bytes locations events after INPUT SOURCE))).
Qed.
End SOURCE.

Definition compiled_reporting_contract assembly index
 (matches : index -> Clight.state -> Asm.state -> Prop) :=
 forall cell base sequence input ofs r digest mode mode_bytes locations observe,
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 runtime_contract result_ge cell observe(sender_initial Int.one sequence input ofs Kstop base) ->
 forall i initial,
 matches i(sender_initial Int.one sequence input ofs Kstop base)initial ->
 (forall trace after,
   star Asm.step (Genv.globalenv assembly) initial trace after ->
   exists rest,outgoing_frame sequence r digest=trace_bytes observe trace++rest) /\
 (forall trace after,
   star Asm.step (Genv.globalenv assembly) initial trace after ->
   Asm.final_state after Int.zero ->
   LeanCageM4_Normalized_decode(imported_bytes(trace_bytes observe trace))=
     LeanCage_Reporting_decodeFrame(source_frame sequence r digest)).

Theorem current_reporting_backend oracle assembly :
 backend_match oracle RuntimeProgram.program assembly ->
 exists index order matches,
 fsim_properties(Clight.semantics2 RuntimeProgram.program)(Asm.semantics assembly)index order matches /\
 compiled_reporting_contract assembly index matches.
Proof.
 intro COMPILE.
 destruct(backend_semantic_preservation _ _ _ COMPILE)as[index order matches PROPS].
 exists index,order,matches;split;[exact PROPS|].
 intros cell base sequence input ofs r digest mode mode_bytes locations observe INPUT RUNTIME i initial MATCH.
 assert(PROGRESS:forall trace after,
   Star (Clight.semantics2 RuntimeProgram.program)(sender_initial Int.one sequence input ofs Kstop base)trace after ->
   (exists result,Clight.final_state after result) \/
   (exists trace next,Clight.step2 result_ge after trace next)).
 { intros trace after RUN;eapply sender_stock_progress;[exact INPUT|exact RUNTIME|exact RUN]. }
 split.
 - intros trace after RUN.
   destruct(@matched_compiler_prefix (Clight.semantics2 RuntimeProgram.program)(Asm.semantics assembly)
     index order matches PROPS i (sender_initial Int.one sequence input ofs Kstop base)
     initial trace after (clight2_receptive RuntimeProgram.program)(Asm.semantics_determinate assembly)
     MATCH PROGRESS RUN)as[source SOURCE].
   eapply sender_stock_prefix;[exact INPUT|exact RUNTIME|exact SOURCE].
 - intros trace after RUN FINAL.
   destruct(@matched_compiler_return (Clight.semantics2 RuntimeProgram.program)(Asm.semantics assembly)
     index order matches PROPS i (sender_initial Int.one sequence input ofs Kstop base)
     initial trace after Int.zero (clight2_receptive RuntimeProgram.program)(Asm.semantics_determinate assembly)
     MATCH PROGRESS RUN FINAL)
     as[source[SOURCE RETURN]].
   inversion RETURN;subst.
   eapply sender_stock_decodes;[exact INPUT|exact RUNTIME|exact SOURCE].
Qed.
