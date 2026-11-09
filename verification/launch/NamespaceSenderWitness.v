(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: A useful admitted publication retains genuine errno for checked release. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine Library LibraryMachine FreshMemory FrameRecord ClightSteps StoreSteps LocalAccess CallContexts
  CallAccess DecoderControl DecoderValidity ErrorNumber WriteMemory.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryReporting Require Import ResultLayout Fault LibraryPreservation SenderSource SenderStorage SenderSelectors SenderEncodingPrefix
  SenderAccess SenderGuards SenderEncoding SenderLastReport SenderReturn SenderReportingSteps SenderReportMemory
  SenderProgram CopyPaths CopyTrace WriteAll WriteCallers.
From EntryNamespace Require Import NamespaceParentFrame NamespaceParentWitness.
Import ListNotations.
Open Scope Z_scope.
Lemma admitted_result_environment:result_ge=Clight.globalenv EntrySource.prog.
Proof. reflexivity. Qed.
Local Opaque result_ge.

Definition admitted_guard_env tag le:=
  PTree.set(guard_flag_temp tag)(Vint Int.zero)(PTree.set(guard_enabled_temp tag)(Vint Int.zero)
    (PTree.set(guard_kind_temp tag)(Vint(Int.repr 5))le)).

Lemma admitted_guard_source memory result_local bytes_local run uid millis digest le tag tail k:
  frame_result_owned memory result_local 0(namespace_admitted_record run uid millis)digest ->
  le!_fd=Some(Vint(Int.repr 8)) ->
  exists count after,after!_fd=Some(Vint(Int.repr 8)) /\
    store_path result_ge(fun current=>current=memory)
      (State f_send_frame(report_stage tag)(Kseq tail k)(sender_env result_local bytes_local)le memory)count
      (State f_send_frame tail k(sender_env result_local bytes_local)after memory).
Proof.
  intros OWN FD;rewrite report_stage_source;unfold guard_prefix.
  eexists;eexists;split.
  2:{
  Ltac admitted_guard_run tag tail record OWN:=
    lazymatch goal with|-store_path _ _ (State _ ?statement _ _ _ _) _ _=>
      first[constr_eq statement tail;apply store_done;reflexivity|
      lazymatch statement with
      |(if ?condition then ?positive else ?negative)=>
        let choice:=eval vm_compute in condition in
        lazymatch choice with
        |true=>change(if condition then positive else negative)with positive
        |false=>change(if condition then positive else negative)with negative
        end;admitted_guard_run tag tail record OWN
      |Sset _ (Efield _ _ _)=>
        eapply store_next;[reflexivity|eapply certified_set_edge;sender_field record OWN|];
          admitted_guard_run tag tail record OWN
      |Sset _ _=>eapply store_next;[reflexivity|apply unchanged_store_edge;eapply edge_set;guard_expression tag|];
          admitted_guard_run tag tail record OWN
      |Sifthenelse _ _ _=>eapply store_next;[reflexivity|apply unchanged_store_edge;eapply edge_if;
          [guard_expression tag|first[reflexivity|apply boolean_condition|apply boolean_typed_condition]]|];
          admitted_guard_run tag tail record OWN
      |_=>eapply store_next;[reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|];
          admitted_guard_run tag tail record OWN
      end]
    end.
  admitted_guard_run tag tail (namespace_admitted_record run uid millis) OWN. }
  guard_lookup tag.
Qed.

Lemma admitted_reporting_parts:
  sender_reporting=Ssequence(report_stage wrong_sequence)
    (Ssequence(report_stage bad_reserved)(Ssequence(report_stage duplicate_frame)
      (Ssequence(report_stage short_frame)(Ssequence(report_stage drop_frame)sender_final_write)))).
Proof. reflexivity. Qed.

Theorem admitted_reports_source memory result_local bytes_local run uid millis digest le k:
  frame_result_owned memory result_local 0(namespace_admitted_record run uid millis)digest ->
  le!_fd=Some(Vint(Int.repr 8)) ->
  exists count after,after!_fd=Some(Vint(Int.repr 8)) /\
    store_path result_ge(fun current=>current=memory)
      (State f_send_frame sender_reporting k(sender_env result_local bytes_local)le memory)count
      (State f_send_frame sender_final_write k(sender_env result_local bytes_local)after memory).
Proof.
  intros OWN FD.
  set(t4:=Ssequence(report_stage drop_frame)sender_final_write).
  set(t3:=Ssequence(report_stage short_frame)t4).
  set(t2:=Ssequence(report_stage duplicate_frame)t3).
  set(t1:=Ssequence(report_stage bad_reserved)t2).
  destruct(admitted_guard_source memory result_local bytes_local run uid millis digest le wrong_sequence t1 k OWN FD)as[n0[l0[F0 P0]]].
  destruct(admitted_guard_source memory result_local bytes_local run uid millis digest l0 bad_reserved t2 k OWN F0)as[n1[l1[F1 P1]]].
  destruct(admitted_guard_source memory result_local bytes_local run uid millis digest l1 duplicate_frame t3 k OWN F1)as[n2[l2[F2 P2]]].
  destruct(admitted_guard_source memory result_local bytes_local run uid millis digest l2 short_frame t4 k OWN F2)as[n3[l3[F3 P3]]].
  destruct(admitted_guard_source memory result_local bytes_local run uid millis digest l3 drop_frame sender_final_write k OWN F3)as[n4[l4[F4 P4]]].
  eexists;exists l4;split;[exact F4|]. rewrite admitted_reporting_parts.
  eapply store_path_trans.
  - eapply store_next;[reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|exact P0].
  - unfold t1;eapply store_path_trans.
    + eapply store_next;[reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|exact P1].
    + unfold t2;eapply store_path_trans.
      * eapply store_next;[reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|exact P2].
      * unfold t3;eapply store_path_trans.
        -- eapply store_next;[reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|exact P3].
        -- unfold t4;eapply store_next;[reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|exact P4].
Qed.

Lemma admitted_sender_free_ready cell before after result_local bytes_local:
  result_local<>tls_block cell ->bytes_local<>tls_block cell ->
  entry_errno_ready cell before ->
  Mem.free_list before(blocks_of_env result_ge(sender_env result_local bytes_local))=Some after ->
  entry_errno_ready cell after.
Proof.
  intros RESULT BYTES READY FREE;rewrite sender_environment_blocks in FREE;cbn[Mem.free_list]in FREE.
  destruct(Mem.free before bytes_local 0 160)as[middle|]eqn:FIRST;[|discriminate].
  destruct(Mem.free middle result_local 0 144)as[final|]eqn:SECOND;[|discriminate].
  inversion FREE;subst final;eapply namespace_errno_unchanged;
    [|eapply Mem.free_unchanged_on;[exact SECOND|intros position RANGE SAME;exact(RESULT SAME)]].
  eapply namespace_errno_unchanged;[exact READY|].
  eapply Mem.free_unchanged_on;[exact FIRST|intros position RANGE SAME;exact(BYTES SAME)].
Qed.

Theorem admitted_sender_returns_ready cell base sequence input run uid millis digest mode mode_bytes locations:
  sender_input cell base input 0(namespace_admitted_record run uid millis)digest mode mode_bytes locations ->
  entry_errno_ready cell base ->
  exists events after,
    library_steps result_ge cell
      (live(sender_initial(Int.repr 8)sequence input 0 Kstop base))events
      (live(Returnstate(Vint Int.zero)Kstop after)) /\entry_errno_ready cell after.
Proof.
  intros[OWN[SELECTORS[magic[SYMBOL MAGIC]]]]READY.
  destruct(copy_reaches_quiet_run result_ge cell _ _ _
    (sender_encoding_connection base(Int.repr 8)sequence input 0(namespace_admitted_record run uid millis)digest Kstop magic
      OWN SYMBOL MAGIC))as[prefix[last[ENCODE[PROGRESS[EMPTY ENCODED]]]]].
  destruct ENCODED as(result_local &bytes_local &le &encoded &STATE &FD &SEQ &RESULT_FRESH &BYTES_FRESH &SEPARATE &STORAGE);subst last.
  pose proof STORAGE as[OLD[FRAME[BYTES[RESULT_FREE BYTES_FREE]]]].
  assert(ENCODED_READY:entry_errno_ready cell encoded).
  { eapply namespace_errno_unchanged;[exact READY|].
    eapply Mem.unchanged_on_implies;[exact OLD|].
    intros object position SAME VALID;subst object.
    destruct READY as[error[LOW[HIGH[ACCESS LOAD]]]].
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(RESULT_TLS:result_local<>tls_block cell)by(eapply fresh_tls_separate;[exact(proj1 SELECTORS)|exact RESULT_FRESH]).
  assert(BYTES_TLS:bytes_local<>tls_block cell)by(eapply fresh_tls_separate;[exact(proj1 SELECTORS)|exact BYTES_FRESH]).
  destruct(admitted_reports_source encoded result_local bytes_local run uid millis digest le Kstop FRAME FD)as[guard_count[reported_le[REPORTED_FD GUARDS]]].
  set(bytes:=outgoing_frame sequence(namespace_admitted_record run uid millis)digest).
  assert(LENGTH:length bytes=160%nat).
  { apply outgoing_frame_length;exact(proj1(proj2(proj2(proj2(proj2 OWN))))). }
  set(q:=sender_request cell(Int.repr 8)bytes_local 160).
  assert(WRITE_OWN:write_owned q bytes encoded).
  { pose proof(sender_frame_write_owned cell encoded(Int.repr 8)bytes_local bytes 160
      (entry_errno_ready_tls _ _ ENCODED_READY)BYTES_TLS BYTES LENGTH ltac:(lia))as INPUT.
    rewrite firstn_all2 in INPUT by lia;exact INPUT. }
  set(return_statement:=Sreturn(Some(Etempvar _t'18 tint))).
  set(suffix:=Kcall(Some _t'18)f_send_frame(sender_env result_local bytes_local)reported_le(Kseq return_statement Kstop)).
  assert(CALL:store_path result_ge(fun current=>current=encoded)
    (State f_send_frame sender_final_write Kstop(sender_env result_local bytes_local)reported_le encoded)2
    (write_call_initial q suffix encoded)).
  { unfold sender_final_write,suffix,return_statement;change(statement_drop 5 sender_reporting)with
      (Ssequence(Scall(Some _t'18)(Evar _write_all(Tfunction[tint;tptr tvoid;tulong]tint cc_default))
        [Etempvar _fd tint;Evar _bytes(tarray tuchar 160);Esizeof(tarray tuchar 160)tulong])
        (Sreturn(Some(Etempvar _t'18 tint)))).
    eapply store_next;[reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|].
    eapply store_next;[reflexivity|eapply sender_write_call_edge with(cell:=cell)(count:=160%nat)
      (count_value:=Vlong(Int64.repr 160));
      [exact REPORTED_FD|apply sizeof_expression_value|reflexivity]|apply store_done;reflexivity]. }
  destruct(write_caller_success q bytes encoded suffix WRITE_OWN I)as[write_events[WRITE_RUN WRITE_BYTES]].
  assert(CELL:cell_of q=cell)by(unfold q;apply sender_request_cell).
  rewrite CELL,<-admitted_result_environment in WRITE_RUN.
  destruct(sender_free_exists cell base encoded result_local bytes_local RESULT_FRESH BYTES_FRESH SEPARATE
    (old_sender_preserved cell _ _ OLD)RESULT_FREE BYTES_FREE)as[after[FREE[AFTER FREED]]].
  assert(RETURN:store_path result_ge(fun current=>current=encoded\/current=after)
    (Returnstate(Vint Int.zero)suffix encoded)3(Returnstate(Vint Int.zero)Kstop after)).
  { unfold suffix,return_statement;eapply store_next;[left;reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|].
    eapply store_next;[left;reflexivity|apply unchanged_store_edge;EntryReporting.WriteAll.structural|].
    eapply store_next;[left;reflexivity|eapply sender_source_return|apply store_done;right;reflexivity].
    - apply old_expression_value,value_temp;apply PTree.gss.
    - reflexivity.
    - exact FREE. }
  exists(prefix++map original_event(repeat(source_step E0)guard_count)++
    map original_event(repeat(source_step E0)2)++map original_event write_events++
    map original_event(repeat(source_step E0)3)),after;split.
  - eapply library_steps_trans;[exact ENCODE|].
    eapply library_steps_trans;[apply original_runs_preserved;eapply store_path_actual;exact GUARDS|].
    eapply library_steps_trans;[apply original_runs_preserved;eapply store_path_actual;exact CALL|].
    eapply library_steps_trans;[exact WRITE_RUN|].
    apply original_runs_preserved;eapply store_path_actual;exact RETURN.
  - exact(admitted_sender_free_ready cell encoded after result_local bytes_local
      RESULT_TLS BYTES_TLS ENCODED_READY FREE).
Qed.
