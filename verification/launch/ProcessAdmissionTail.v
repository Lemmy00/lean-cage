(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Actual helper success requires ordered full placement and options. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll WriteMemory.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessReturns
  ProcessPaths ProcessCalls ProcessContexts ProcessCallee ProcessPlacement ProcessAdmissionEvents.
From EntryProcess Require Import ProcessPrimitiveCases.
From LeanCageMainNumber Require Import NumberInitial.
Import ListNotations.
Open Scope Z_scope.

Definition admission_placement_cont locals le :=
  admission_write_cont locals le(Kseq(admission_tail 11(fn_body f_admit_child))Kstop).
Definition admission_final_options_cont locals le :=
  admission_options_cont locals(PTree.set _t'6(Vint Int.zero)le)(Kseq admission_return Kstop).

Lemma admission_request_cell cell locals cgroup count :
  cell_of(admission_write_request cell locals cgroup count)=cell.
Proof. destruct cell;reflexivity. Qed.

Theorem admission_tail_write_source locals le memory count cgroup :
  le!_cgfd=Some(Vint cgroup) ->le!_pidlength=Some(Vint count) ->
  store_path admission_ge(fun _=>True)
    (State f_admit_child(admission_tail 10(fn_body f_admit_child))Kstop(admission_env locals)le memory)3
    (Callstate(Internal f_write_all)
      [Vint cgroup;Vptr(admission_text locals)Ptrofs.zero;Vlong(Int64.repr(Int.signed count))]
      (admission_placement_cont locals le)memory).
Proof.
  intros CGROUP COUNT.
  change(admission_tail 10(fn_body f_admit_child))with
    (Ssequence admission_place(admission_tail 11(fn_body f_admit_child))).
  admission_route;eapply number_path_implication with(P:=fun current=>current=memory).
  - intros;exact I.
  - apply admission_write_call_source;assumption.
Qed.

Theorem admission_write_to_options_source locals le memory child :le!_child=Some(Vint child) ->
  store_path admission_ge(fun _=>True)
    (Returnstate(Vint Int.zero)(admission_placement_cont locals le)memory)7
    (Callstate process_ptrace_definition
      [Vint(Int.repr 16896);Vint child;Vlong Int64.zero;Vlong(Int64.repr 1048592)]
      (admission_final_options_cont locals le)memory).
Proof.
  intro CHILD;unfold admission_placement_cont,admission_final_options_cont.
  eapply store_path_trans with(n:=3%nat).
  - eapply number_path_implication with(P:=fun current=>current=memory);[intros;exact I|].
    pose proof(admission_write_return_source locals le memory Int.zero
      (Kseq(admission_tail 11(fn_body f_admit_child))Kstop))as RETURN.
    rewrite Int.eq_true in RETURN;exact RETURN.
  - admission_route.
    change(admission_tail 11(fn_body f_admit_child))with(Ssequence admission_options admission_return).
    admission_route;eapply number_path_implication with(P:=fun current=>current=memory);[intros;exact I|].
    apply admission_options_call_source;rewrite PTree.gso by discriminate;exact CHILD.
Qed.

Lemma admission_final_options_source locals le memory:
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

Lemma admission_final_return_quiet cell locals le memory events after:
  process_steps admission_ge cell
    (live(State f_admit_child admission_return Kstop(admission_env locals)le memory))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->Forall admission_quiet_event events.
Proof.
  intro RUN;rewrite admission_finish_source in RUN;inversion RUN;subst;try discriminate.
  match goal with STEP:process_step _ _ _ _ _|-_=>
    destruct(process_return_statement_terminates admission_ge cell f_admit_child(Econst_int Int.zero tint)
      Kstop(admission_env locals)le memory _ _(Logic.eq_refl _)STEP)
      as[[EVENT[returned[observed TARGET]]]|[EVENT TARGET]]end;subst.
  - match goal with TAIL:process_steps _ _ (live(Returnstate _ Kstop _)) _ _|-_=>
      destruct(process_terminal_run_constant _ _ _ _ _ _ _ TAIL)as[EVENTS REST]end;subst.
    constructor;[left;reflexivity|constructor].
  - match goal with TAIL:process_steps _ _ (dead _) _ _|-_=>
      destruct(process_dead_steps _ _ _ _ _ TAIL)as[EVENTS IMPOSSIBLE];discriminate end.
Qed.

Theorem admission_final_options_quiet cell locals le memory events after:
  process_steps admission_ge cell
    (live(Returnstate(Vlong Int64.zero)(admission_final_options_cont locals le)memory))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->Forall admission_quiet_event events.
Proof.
  intro RUN.
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (admission_final_options_source locals le memory)ltac:(intros;discriminate)RUN)
    as[rest[EVENTS FINISH]].
  rewrite EVENTS;apply Forall_app;split;[apply admission_source_quiet|].
  eapply admission_final_return_quiet;exact FINISH.
Qed.

Theorem admission_success_requires_placement_options_with_tail cell locals le memory child cgroup count input events after :
  le!_child=Some(Vint child) ->le!_cgfd=Some(Vint cgroup) ->le!_pidlength=Some(Vint count) ->
  write_owned(admission_write_request cell locals cgroup count)input memory ->input<>[] ->
  process_cgroup_whole_returns cgroup events ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 10(fn_body f_admit_child))Kstop(admission_env locals)le memory))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists error before_write before_options suffix,
    events=before_write++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer input error))::
      (before_options++process_traced(Int.repr 16896)child(Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero::suffix) /\
    Forall admission_passive_event before_write /\Forall admission_quiet_event before_options /\
    Forall admission_quiet_event suffix.
Proof.
  intros CHILD CGROUP COUNT OWN NONEMPTY WHOLE RUN.
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
    assert(WHOLE_WRITER:process_cgroup_whole_returns(IO.descriptor q)writer).
    { intros actual bytes error MEMBER DESCRIPTOR WRITING;eapply WHOLE;[|exact DESCRIPTOR|exact WRITING].
      rewrite EVENTS,SPLIT;apply in_or_app;right;apply in_or_app;left;exact MEMBER. }
    destruct(current_cgroup_process_return_split q input memory writer written OWN NONEMPTY WRITER WHOLE_WRITER)
      as[_[error[before_write[after_write[WRITE_EVENTS PURE]]]]].
    assert(PASSIVE_WRITE:Forall admission_passive_event before_write).
    { assert(PASSIVE:Forall admission_passive_event writer)by(rewrite ORIGINAL;apply admission_original_passive).
      rewrite WRITE_EVENTS in PASSIVE;apply Forall_app in PASSIVE;exact(proj1 PASSIVE). }
    destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
      (admission_write_to_options_source locals le written child CHILD)ltac:(intros;discriminate)REST)
      as[options[CONTINUATION OPTIONS]].
    destruct(process_ptrace_return_decomposition _ _ _ _ _ _ _ _ _ _ _ OPTIONS)
      as[waiting[returned[observed[rest[OPTION_EVENTS[FRAME[READY FINISH]]]]]]].
    pose proof(admission_options_return_source locals(PTree.set _t'6(Vint Int.zero)le)
      observed returned(Kseq admission_return Kstop))as OPTION_RETURN.
    destruct(Int64.eq returned Int64.zero)eqn:OK.
    + apply Int64.same_if_eq in OK;subst returned.
      exists error,(repeat process_source_event 3++before_write),
        (after_write++(repeat process_source_event 7++repeat process_waiting waiting)),rest.
      split.
      * rewrite EVENTS,SPLIT,WRITE_EVENTS,CONTINUATION,OPTION_EVENTS;
          repeat first[rewrite <-app_assoc|progress(cbn[app])];reflexivity.
      * split.
        -- apply Forall_app;split;[apply admission_source_passive|exact PASSIVE_WRITE].
        -- split.
           ++ repeat rewrite Forall_app;split;[apply admission_pure_quiet;exact PURE|].
              split;[apply admission_source_quiet|apply admission_waiting_quiet].
           ++ eapply admission_final_options_quiet;exact FINISH.
    + destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
        OPTION_RETURN ltac:(intros;discriminate)FINISH)as[failure[FAILED IMPOSSIBLE]].
      exfalso;eapply process_negative_return_cannot_zero with(fn:=f_admit_child)
        (k:=Kseq admission_return Kstop);[reflexivity|reflexivity|exact IMPOSSIBLE].
  - destruct BAD as[VALUE OTHER];subst returned.
    pose proof(admission_write_return_source locals le written Int.mone
      (Kseq(admission_tail 11(fn_body f_admit_child))Kstop))as WRITE_RETURN.
    change(Int.eq Int.mone Int.zero)with false in WRITE_RETURN.
    destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
      WRITE_RETURN ltac:(intros;discriminate)REST)as[failure[FAILED IMPOSSIBLE]].
    exfalso;eapply process_negative_return_cannot_zero with(fn:=f_admit_child)
      (k:=Kseq(admission_tail 11(fn_body f_admit_child))Kstop);[reflexivity|reflexivity|exact IMPOSSIBLE].
Qed.

Theorem admission_success_requires_placement_options cell locals le memory child cgroup count input events after :
  le!_child=Some(Vint child) ->le!_cgfd=Some(Vint cgroup) ->le!_pidlength=Some(Vint count) ->
  write_owned(admission_write_request cell locals cgroup count)input memory ->input<>[] ->
  process_cgroup_whole_returns cgroup events ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 10(fn_body f_admit_child))Kstop(admission_env locals)le memory))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists error before_write before_options suffix,
    events=before_write++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer input error))::
      (before_options++process_traced(Int.repr 16896)child(Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero::suffix) /\
    Forall admission_passive_event before_write /\Forall admission_quiet_event before_options.
Proof.
  intros CHILD CGROUP COUNT OWN NONEMPTY WHOLE RUN.
  destruct(admission_success_requires_placement_options_with_tail _ _ _ _ _ _ _ _ _ _
    CHILD CGROUP COUNT OWN NONEMPTY WHOLE RUN)
    as[error[before_write[before_options[suffix[EVENTS[PASSIVE[QUIET TAIL]]]]]]].
  exists error,before_write,before_options,suffix;auto.
Qed.
