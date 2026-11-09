(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Establish descriptor stability before using the owned cgroup's write law. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine StoreSteps WriteAll WriteMemory ErrorNumber.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffFormat.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessPaths ProcessReturns
  ProcessCallee ProcessCalls ProcessContexts ProcessWait ProcessPrimitiveCases ProcessNumeric ProcessPlacement ProcessOwnership ProcessAdmissionEvents
  ProcessAdmissionBridge ProcessAdmissionTail ProcessAdmissionNumeric ProcessAdmissionFormat ProcessAdmissionWait.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberInitial.
Import ListNotations.
Open Scope Z_scope.

Definition admission_file_event event := process_file_frame_event event=true.

Lemma admission_file_sources count :Forall admission_file_event(repeat process_source_event count).
Proof. apply admission_repeat_forall;reflexivity. Qed.

Lemma admission_passive_live_files ge cell initial events final :
  process_steps ge cell initial events(live final) ->Forall admission_passive_event events ->
  Forall admission_file_event events.
Proof.
  intros RUN CLASS;pose proof(admission_passive_leases Int.zero(tls_block cell)Ptrofs.zero events CLASS)as LEASE.
  apply Forall_forall;intros event MEMBER.
  apply Forall_forall with(x:=event)in LEASE;[|exact MEMBER].
  exact(proj2(admission_lease_live_member_flags _ _ _ _ _ Int.zero(tls_block cell)Ptrofs.zero event
    RUN MEMBER LEASE)).
Qed.

Lemma admission_finish_live_files cell locals le memory k events after :
  call_cont k=Kstop ->
  process_steps admission_ge cell
    (live(State f_admit_child admission_return k(admission_env locals)le memory))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->Forall admission_file_event events.
Proof.
  intros CLOSED RUN;rewrite admission_finish_source in RUN;inversion RUN;subst;try discriminate.
  match goal with STEP:process_step _ _ _ _ _|-_=>
    destruct(process_return_statement_terminates _ _ _ _ _ _ _ _ _ _ CLOSED STEP)
      as[[EVENT[returned[observed TARGET]]]|[EVENT TARGET]]end;subst.
  - match goal with TAIL:process_steps _ _ (live(Returnstate _ Kstop _)) _ _|-_=>
      destruct(process_terminal_run_constant _ _ _ _ _ _ _ TAIL)as[EVENTS REST]end;subst.
    constructor;[reflexivity|constructor].
  - match goal with TAIL:process_steps _ _ (dead _) _ _|-_=>
      destruct(process_dead_steps _ _ _ _ _ TAIL)as[EVENTS IMPOSSIBLE];discriminate end.
Qed.

Lemma admission_options_finish_source locals le memory :
  store_path admission_ge(fun _=>True)
    (Returnstate(Vlong Int64.zero)(admission_final_options_cont locals le)memory)4
    (State f_admit_child admission_return Kstop(admission_env locals)
      (PTree.set _t'7(Vlong Int64.zero)(PTree.set _t'6(Vint Int.zero)le))memory).
Proof.
  replace 4%nat with(3+1)%nat by lia;eapply store_path_trans.
  - pose proof(admission_options_return_source locals(PTree.set _t'6(Vint Int.zero)le)
      memory Int64.zero(Kseq admission_return Kstop))as PATH.
    rewrite Int64.eq_true in PATH;eapply number_path_implication;[intros;exact I|exact PATH].
  - admission_route;apply store_done;exact I.
Qed.

Theorem admission_tail_preserves_files cell locals le memory child cgroup count input events after :
  le!_child=Some(Vint child) ->le!_cgfd=Some(Vint cgroup) ->le!_pidlength=Some(Vint count) ->
  write_owned(admission_write_request cell locals cgroup count)input memory ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 10(fn_body f_admit_child))Kstop(admission_env locals)le memory))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->Forall admission_file_event events.
Proof.
  intros CHILD CGROUP COUNT OWN RUN.
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (admission_tail_write_source locals le memory count cgroup CGROUP COUNT)ltac:(intros;discriminate)RUN)
    as[tail[EVENTS CONTINUE]].
  destruct(process_callee_return_decomposition _ _ _ _ _ _ _ _ _
    CONTINUE ltac:(exact I)ltac:(unfold admission_placement_cont,admission_write_cont;discriminate))
    as[writer[continuation[returned[written[SPLIT[WRITE REST]]]]]].
  set(q:=admission_write_request cell locals cgroup count).
  assert(WRITER:process_steps admission_ge(cell_of q)
    (live(Callstate(Internal f_write_all)
      [Vint(IO.descriptor q);Vptr(buffer_block q)(Ptrofs.repr(buffer_offset q));
       Vlong(Int64.repr(requested q))]Kstop memory))writer(live(Returnstate returned Kstop written))).
  { unfold q;rewrite admission_request_cell;exact WRITE. }
  destruct(current_write_process_return q input memory writer returned written OWN WRITER)
    as[original[ORIGINAL[PRESERVED[GOOD|BAD]]]].
  - destruct GOOD as[VALUE EMITTED];subst returned.
    assert(WRITER_FILES:Forall admission_file_event writer).
    { eapply admission_passive_live_files;[exact WRITER|rewrite ORIGINAL;apply admission_original_passive]. }
    destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
      (admission_write_to_options_source locals le written child CHILD)ltac:(intros;discriminate)REST)
      as[options[CONTINUATION OPTIONS]].
    destruct(process_ptrace_return_decomposition _ _ _ _ _ _ _ _ _ _ _ OPTIONS)
      as[waiting[returned[observed[rest[OPTION_EVENTS[FRAME[READY FINISH]]]]]]].
    destruct(Int64.eq returned Int64.zero)eqn:OK.
    + apply Int64.same_if_eq in OK;subst returned.
      destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
        (admission_options_finish_source locals le observed)ltac:(intros;discriminate)FINISH)
        as[finished[FINISHED RETURN]].
      assert(FILES:Forall admission_file_event finished)
        by(eapply admission_finish_live_files with(k:=Kstop);[reflexivity|exact RETURN]).
      rewrite EVENTS,SPLIT,CONTINUATION,OPTION_EVENTS,FINISHED.
      repeat rewrite Forall_app;repeat split;try apply admission_file_sources;try exact WRITER_FILES.
      * apply admission_repeat_forall;reflexivity.
      * constructor;[reflexivity|]. apply Forall_app;split;[apply admission_file_sources|exact FILES].
    + pose proof(admission_options_return_source locals(PTree.set _t'6(Vint Int.zero)le)
        observed returned(Kseq admission_return Kstop))as OPTION_RETURN;rewrite OK in OPTION_RETURN.
      destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
        OPTION_RETURN ltac:(intros;discriminate)FINISH)as[failure[FAILED IMPOSSIBLE]].
      exfalso;eapply process_negative_return_cannot_zero with(fn:=f_admit_child)(k:=Kseq admission_return Kstop);
        [reflexivity|reflexivity|exact IMPOSSIBLE].
  - destruct BAD as[VALUE OTHER];subst returned.
    pose proof(admission_write_return_source locals le written Int.mone
      (Kseq(admission_tail 11(fn_body f_admit_child))Kstop))as WRITE_RETURN.
    change(Int.eq Int.mone Int.zero)with false in WRITE_RETURN.
    destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
      WRITE_RETURN ltac:(intros;discriminate)REST)as[failure[FAILED IMPOSSIBLE]].
    exfalso;eapply process_negative_return_cannot_zero with(fn:=f_admit_child)
      (k:=Kseq(admission_tail 11(fn_body f_admit_child))Kstop);[reflexivity|reflexivity|exact IMPOSSIBLE].
Qed.

Theorem admission_numeric_preserves_files cell locals formatting_before before original child cgroup count events after :
  original!_child=Some(Vint child) ->1<=Int.signed child ->
  original!_cgfd=Some(Vint cgroup) ->original!_pidlength=Some(Vint count) ->
  entry_format_result cell formatting_before(admission_text locals)Ptrofs.zero count before ->
  number_output before(admission_encoded locals)Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  admission_text locals<>tls_block cell ->admission_encoded locals<>tls_block cell ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 5(fn_body f_admit_child))Kstop(admission_env locals)original before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->Forall admission_file_event events.
Proof.
  intros CHILD POSITIVE CGROUP COUNT FORMATTED OUTPUT DISTINCT TEXT_TLS ENCODED_TLS RUN.
  destruct(admission_numeric_source cell locals formatting_before before original child count Kstop
    CHILD ltac:(lia)COUNT FORMATTED OUTPUT DISTINCT)as[used[last[PATH[BOUND LEAF]]]].
  assert(NOT_RETURN:forall value memory,last<>Returnstate value Kstop memory).
  { intros value memory SAME;destruct LEAF as[[m[le[k[STATE REST]]]]|[m[le[bytes[first[rest[STATE FACTS]]]]]]];
      subst last;discriminate. }
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _ PATH NOT_RETURN RUN)
    as[rest[EVENTS CONTINUE]].
  destruct LEAF as[[memory[le[k[STATE[CLOSED FRAME]]]]]|[memory[le[bytes[first[remaining
    [STATE[FRAME[LENGTH[EXTENT[BYTES[LEADING[DIGITS[VALUE[INPUT POST]]]]]]]]]]]]]]].
  - subst last;exfalso;eapply process_negative_return_cannot_zero with(fn:=f_admit_child)(k:=k);
      [reflexivity|exact CLOSED|exact CONTINUE].
  - subst last.
    assert(CHILD':le!_child=Some(Vint child)).
    { rewrite(FRAME _child ltac:(cbn;intuition discriminate));exact CHILD. }
    assert(CGROUP':le!_cgfd=Some(Vint cgroup)).
    { rewrite(FRAME _cgfd ltac:(cbn;intuition discriminate));exact CGROUP. }
    assert(COUNT':le!_pidlength=Some(Vint count)).
    { rewrite(FRAME _pidlength ltac:(cbn;intuition discriminate));exact COUNT. }
    destruct(admission_number_errno_ready cell before(admission_encoded locals)(Int.signed child)memory
      ENCODED_TLS(entry_format_errno _ _ _ _ _ _ FORMATTED)POST)as[error ERRNO].
    assert(OWN:write_owned(admission_write_request cell locals cgroup count)bytes memory).
    { eapply admission_write_owned;[exact INPUT|exact LENGTH|lia|exact ERRNO|exact TEXT_TLS]. }
    rewrite EVENTS;apply Forall_app;split;[apply admission_file_sources|].
    eapply admission_tail_preserves_files;
      [exact CHILD'|exact CGROUP'|exact COUNT'|exact OWN|exact CONTINUE].
Qed.

Theorem admission_formatter_preserves_files cell locals before original child cgroup events after :
  original!_child=Some(Vint child) ->1<=Int.signed child ->original!_cgfd=Some(Vint cgroup) ->
  number_output before(admission_encoded locals)Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  admission_text locals<>tls_block cell ->admission_encoded locals<>tls_block cell ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 4(fn_body f_admit_child))Kstop(admission_env locals)original before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->Forall admission_file_event events.
Proof.
  intros CHILD POSITIVE CGROUP OUTPUT DISTINCT TEXT_TLS ENCODED_TLS RUN.
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (admission_format_call_source locals original before child CHILD)ltac:(intros;discriminate)RUN)
    as[tail[EVENTS CONTINUE]].
  destruct(admission_format_return_decomposition _ _ _ _ _ _ _ _ _ _ CONTINUE)
    as[waiting[count[formatted[rest[FORMATTED[RESULT REST]]]]]].
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (admission_format_return_source locals original formatted count Kstop)ltac:(intros;discriminate)REST)
    as[numeric[NUMERIC RUN_NUMERIC]].
  assert(CHILD':(admission_format_returned original count)!_child=Some(Vint child)).
  { unfold admission_format_returned;repeat rewrite PTree.gso by discriminate;exact CHILD. }
  assert(CGROUP':(admission_format_returned original count)!_cgfd=Some(Vint cgroup)).
  { unfold admission_format_returned;repeat rewrite PTree.gso by discriminate;exact CGROUP. }
  assert(COUNT':(admission_format_returned original count)!_pidlength=Some(Vint count)).
  { unfold admission_format_returned;apply PTree.gss. }
  assert(OUTPUT':number_output formatted(admission_encoded locals)Ptrofs.zero)
    by(eapply admission_format_preserves_output;eassumption).
  rewrite EVENTS,FORMATTED,NUMERIC.
  apply Forall_app;split;[apply admission_file_sources|].
  apply Forall_app;split;[apply admission_repeat_forall;reflexivity|].
  constructor;[reflexivity|]. apply Forall_app;split;[apply admission_file_sources|].
  eapply admission_numeric_preserves_files;
    [exact CHILD'|exact POSITIVE|exact CGROUP'|exact COUNT'|exact RESULT|exact OUTPUT'|
      exact DISTINCT|exact TEXT_TLS|exact ENCODED_TLS|exact RUN_NUMERIC].
Qed.

Theorem admission_actual_file_frames_from_live_tls cell before child cgroup status offset events after :
  1<=Int.signed child ->status<>tls_block cell ->Mem.valid_block before(tls_block cell) ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status offset]Kstop before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->Forall admission_file_event events.
Proof.
  intros POSITIVE SEPARATE ERRNO RUN.
  destruct(admission_allocate before)as[locals[allocated[ALLOC OBJECTS]]].
  destruct(admission_fresh_storage_from_live_tls _ _ _ _ ERRNO OBJECTS)as[DISTINCT[TEXT_TLS[ENCODED_TLS OUTPUT]]].
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (admission_start_to_wait before locals allocated child cgroup status offset Kstop ALLOC)
    ltac:(intros;discriminate)RUN)as[waiting[EVENTS WAIT]].
  destruct(admission_parameter_bindings child cgroup(Vptr status offset))as[CHILD[CGROUP STATUS]].
  destruct(admission_wait_to_formatter cell locals allocated
    (admission_parameters child cgroup(Vptr status offset))child cgroup status offset waiting after
    POSITIVE SEPARATE CHILD CGROUP STATUS OUTPUT WAIT)
    as[prefix[tail[actual[memory[word FACTS]]]]].
  destruct FACTS as[ORDER[STOP_EVENT[STOP[SIGNAL[CHILD'[CGROUP'[OUTPUT'[CONTINUE EXTRA]]]]]]]].
  destruct EXTRA as[search[SEARCH CLASS]].
  assert(SEARCH_FILES:Forall admission_file_event search).
  { apply Forall_forall;intros event MEMBER.
    apply Forall_forall with(x:=event)in CLASS;[|exact MEMBER].
    exact(proj2(admission_lease_live_member_flags _ _ _ _ _ child status offset event RUN
      ltac:(rewrite EVENTS,ORDER,SEARCH;apply in_or_app;right;apply in_or_app;left;
        apply in_or_app;left;exact MEMBER)CLASS)). }
  assert(TAIL_FILES:Forall admission_file_event tail).
  { eapply admission_formatter_preserves_files;
      [exact CHILD'|exact POSITIVE|exact CGROUP'|exact OUTPUT'|exact DISTINCT|
        exact TEXT_TLS|exact ENCODED_TLS|exact CONTINUE]. }
  rewrite EVENTS,ORDER,SEARCH.
  apply Forall_app;split;[apply admission_file_sources|].
  apply Forall_app;split;[|exact TAIL_FILES].
  apply Forall_app;split;[exact SEARCH_FILES|].
  constructor;[unfold admission_file_event;cbn[process_file_frame_event process_nonreaping];exact STOP|].
  apply admission_file_sources.
Qed.

Theorem admission_actual_file_frames cell before child cgroup status offset events after :
  1<=Int.signed child ->status<>tls_block cell ->entry_errno_ready cell before ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status offset]Kstop before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->Forall admission_file_event events.
Proof.
  intros POSITIVE SEPARATE READY RUN.
  eapply admission_actual_file_frames_from_live_tls;try eassumption.
  eapply admission_ready_valid;exact READY.
Qed.
