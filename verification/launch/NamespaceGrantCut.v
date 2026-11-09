(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Every actual private parent write crosses the checked grant source call. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess CallContexts WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller ProcessContexts ProcessMemory ProcessClockRun ProcessDescriptor.
From EntryReporting Require Import ResultLayout.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller
  NamespaceRelease NamespaceReporting NamespacePublication NamespaceContexts NamespaceAdmission
  NamespaceClosure NamespaceAdmissionProjection NamespaceTLS NamespaceParentSafety NamespaceTailDescriptor
  NamespaceGrantAuthorization NamespaceGrantRouting NamespaceSocket NamespaceReleaseProjection.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_failed_publication_report_frontier e le memory k report:
  le!_bad=Some(Vint Int.one) ->le!_report=Some(Vint report) ->
  exists count final,final!_bad=Some(Vint Int.one) /\final!_report=Some(Vint report) /\
    namespace_first_call_path namespace_ge
      (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 30)k e final memory)count
      (State f_namespace_init(namespace_tail 29)k e le memory).
Proof.
  intros BAD REPORT;unfold namespace_tail,child_tail;cbn[fn_body].
  eexists;exists(PTree.set _t'17(Vint Int.zero)(PTree.set _t'16(Vint Int.zero)le));split;[WriteAll.lookup|]. split;[WriteAll.lookup|].
  admission_frontier_route;admission_frontier_route;admission_frontier_route.
  eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - admission_frontier_set;[apply old_expression_value,value_int|]. admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + admission_frontier_set;[apply old_expression_value,value_int|]. admission_frontier_route.
      eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_failed_release_report_frontier e le memory k report:
  le!_bad=Some(Vint Int.one) ->le!_report=Some(Vint report) ->
  exists count final,final!_bad=Some(Vint Int.one) /\final!_report=Some(Vint report) /\
    namespace_first_call_path namespace_ge
      (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 31)k e final memory)count
      (State f_namespace_init(namespace_tail 30)k e le memory).
Proof.
  intros BAD REPORT;unfold namespace_tail,child_tail;cbn[fn_body].
  eexists;exists(PTree.set _t'20(Vint Int.zero)le);split;[WriteAll.lookup|]. split;[WriteAll.lookup|].
  admission_frontier_route;admission_frontier_route.
  eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - admission_frontier_set;[apply old_expression_value,value_int|]. admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.


Theorem namespace_tail_private_write_impossible cell e le memory report peer events called arguments continuation final event after:
  caller_env_global e ->le!_report=Some(Vint report) ->report<>peer ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 31)Kstop e le memory))events
    (live(Callstate called arguments continuation final)) ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))event after ->
  ~private_namespace_write peer event.
Proof.
  intros GLOBAL REPORT OTHER RUN STEP PRIVATE.
  pose proof(namespace_steps_append _ _ _ _ _ _ _ RUN
    (namespace_steps_cons _ _ _ _ _ _ _ STEP(namespace_steps_nil _ _ after)))as WHOLE.
  pose proof(actual_namespace_tail_report_descriptors _ _ _ _ _ _ _ GLOBAL REPORT WHOLE)as WRITES.
  rewrite Forall_forall in WRITES;eapply descriptor_excludes_private;
    [exact OTHER|apply WRITES;apply in_or_app;right;left;reflexivity|exact PRIVATE].
Qed.

Theorem namespace_failed_release_private_impossible cell e le memory report peer events called arguments continuation final event after:
  caller_env_global e ->le!_bad=Some(Vint Int.one) ->le!_report=Some(Vint report) ->report<>peer ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 30)Kstop e le memory))events
    (live(Callstate called arguments continuation final)) ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))event after ->
  ~private_namespace_write peer event.
Proof.
  intros GLOBAL BAD REPORT OTHER RUN STEP PRIVATE.
  destruct(namespace_failed_release_report_frontier e le memory Kstop report BAD REPORT)
    as[count[next[BAD'[REPORT' PATH]]]].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  eapply namespace_tail_private_write_impossible;eassumption.
Qed.

Theorem private_write_publication_requires_good cell e le memory report peer events called arguments continuation final event after:
  caller_env_global e ->namespace_bad_binary le ->le!_report=Some(Vint report) ->report<>peer ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 29)Kstop e le memory))events
    (live(Callstate called arguments continuation final)) ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))event after ->
  private_namespace_write peer event ->le!_bad=Some(Vint Int.zero).
Proof.
  intros GLOBAL[GOOD|BAD]REPORT OTHER RUN STEP PRIVATE;[exact GOOD|].
  destruct(namespace_failed_publication_report_frontier e le memory Kstop report BAD REPORT)
    as[count[next[BAD'[REPORT' PATH]]]].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  exfalso;eapply namespace_failed_release_private_impossible;eassumption.
Qed.

Theorem private_write_release_cut cell e le memory child peer report events called arguments continuation final event after:
  caller_env_global e ->namespace_bad_binary le ->le!_report=Some(Vint report) ->report<>peer ->
  le!_launch_child=Some(Vint child) ->le!_launch_peer=Some(Vint peer) ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 30)Kstop e le memory))events
    (live(Callstate called arguments continuation final)) ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))event after ->
  private_namespace_write peer event ->
  exists suffix,events=repeat namespace_source_event 5++suffix /\
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 30)Kstop e le memory))
      (repeat namespace_source_event 5)
      (live(Callstate(Internal f_release_child)[Vint child;Vint peer](namespace_release_cont e le child peer Kstop)memory)) /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_release_child)[Vint child;Vint peer](namespace_release_cont e le child peer Kstop)memory))suffix
      (live(Callstate called arguments continuation final)).
Proof.
  intros GLOBAL[GOOD|BAD]REPORT OTHER CHILD PEER RUN STEP PRIVATE.
  - assert(RELEASE:e!_release_child=None)by(apply GLOBAL;vm_compute;reflexivity).
    destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
      (namespace_authorized_release_first_callback e le memory Kstop child peer GOOD RELEASE CHILD PEER)RUN)
      as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint;exists rest;auto.
  - exfalso;eapply namespace_failed_release_private_impossible;eassumption.
Qed.

Theorem namespace_release_return_report_descriptors cell e le child peer returned memory report events target:
  caller_env_global e ->le!_report=Some(Vint report) ->
  namespace_steps namespace_ge cell
    (live(Returnstate returned(namespace_release_cont e le child peer Kstop)memory))events target ->
  Forall(descriptor_namespace_event report)events.
Proof.
  intros GLOBAL REPORT RUN;change(Forall(tail_descriptor_namespace_event report)events).
  eapply tail_descriptor_actual_namespace_writes;[|exact RUN].
  destruct(namespace_release_suffix_context e le child peer Kstop GLOBAL(conj I I))as[GLOBALS CLOSED].
  split.
  - split;[exact GLOBALS|exact CLOSED].
  - split;[exact I|]. cbn[namespace_release_cont tail_descriptor_cont].
    split;[exact namespace_report_variable_checked|].
    split;[change(le!_report=Some(Vint report));exact REPORT|].
    repeat split;vm_compute;reflexivity.
Qed.

Theorem actual_private_write_inside_release cell e le child peer memory report events called arguments continuation final event after:
  caller_env_global e ->le!_report=Some(Vint report) ->report<>peer ->
  namespace_steps namespace_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer](namespace_release_cont e le child peer Kstop)memory))events
    (live(Callstate called arguments continuation final)) ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))event after ->
  private_namespace_write peer event ->
  exists local next,namespace_steps namespace_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop memory))events(live local) /\
    namespace_step namespace_ge cell(live local)event next.
Proof.
  intros GLOBAL REPORT OTHER RUN WRITE PRIVATE.
  destruct(namespace_caller_run_decomposition namespace_ge cell(namespace_release_cont e le child peer Kstop)
    (Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop memory)events
    (live(Callstate called arguments continuation final))I RUN)
    as[[local[LOCAL SAME]]|[prefix[rest[returned[result[EVENTS[LOCAL REMAINING]]]]]]].
  - destruct local as[current|dead_memory];[|discriminate].
    change(live(Callstate called arguments continuation final)=
      live(plug_state current(namespace_release_cont e le child peer Kstop)))in SAME.
    assert(NOTRETURN:~local_return current).
    { intros[value[other RETURN]];subst current;discriminate SAME. }
    assert(WRITE':namespace_step namespace_ge cell
      (live(plug_state current(namespace_release_cont e le child peer Kstop)))event after).
    { rewrite <-SAME;exact WRITE. }
    destruct(unplug_namespace_step _ _ _ _ _ (namespace_release_cont e le child peer Kstop) I NOTRETURN WRITE')as[next[STEP TARGET]].
    exists current,next;auto.
  - assert(WHOLE:namespace_steps namespace_ge cell
      (live(Returnstate returned(namespace_release_cont e le child peer Kstop)result))(rest++[event])after).
    { eapply namespace_steps_append;[exact REMAINING|econstructor;[exact WRITE|constructor]]. }
    pose proof(namespace_release_return_report_descriptors _ _ _ _ _ _ _ _ _ _ GLOBAL REPORT WHOLE)as FD.
    rewrite Forall_forall in FD;exfalso;eapply descriptor_excludes_private;
      [exact OTHER|apply FD;apply in_or_app;right;left;reflexivity|exact PRIVATE].
Qed.

Theorem actual_private_parent_write_authorized cell e le before childobject pipe child peer cgroup status temporary admission
    report sequence events called arguments continuation final event after:
  caller_env_global e ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->e!_status=Some(status,tint) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  e!__res__6=Some(temporary,result_type) ->e!_admission=Some(admission,result_type) ->
  Mem.load Mint32 before childobject 0=Some(Vint child) ->Mem.load Mint32 before pipe 0=Some(Vint peer) ->
  Mem.load Mint32 before(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 before(namespace_symbol _preflight)0=Some(Vint Int.zero) ->
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  Mem.valid_block before(tls_block cell) ->cgroup<>peer ->report<>peer ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le before))events
    (live(Callstate called arguments continuation final)) ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))event after ->
  private_namespace_write peer event ->
  exists prefix suffix release_temps released local next,events=prefix++suffix /\
    namespace_authorized_parent cell before child peer cgroup status temporary admission report sequence prefix /\
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le before))prefix
      (live(Callstate(Internal f_release_child)[Vint child;Vint peer]
        (namespace_release_cont e release_temps child peer Kstop)released)) /\
    namespace_steps namespace_ge cell(live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop released))suffix
      (live local) /\namespace_step namespace_ge cell(live local)event next.
Proof.
  intros GLOBAL CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION PID PEER CGFD CHECK
    BAD REPORT SEQUENCE TLS CG_OTHER REPORT_OTHER RUN WRITE PRIVATE.
  assert(ADMIT:e!_admit_child=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(CLOSE:e!_close=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(RESULT:e!_result_of=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(CLOCK:e!_now_ms=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(SEND:e!_send_frame=None)by(apply GLOBAL;vm_compute;reflexivity).
  destruct(private_write_after_capture_admit cell e le before Kstop childobject pipe child peer cgroup Int.zero status
    called arguments continuation events final peer event after CG_OTHER WRITE PRIVATE ADMIT STATUS CHILD PIPE CGROUP PREFLIGHT
    PID PEER CGFD CHECK RUN)
    as[admit_events[after_admit[admit_value[admitted[ORDER_ADMIT[ADMIT_RUN[ADMIT_CONTINUE PREFIX_ADMIT]]]]]]].
  pose(namespace_captured:=namespace_launch_env le child peer cgroup Int.zero).
  assert(VALUES:namespace_launch_values namespace_captured child peer cgroup Int.zero)by(apply namespace_launch_values_set).
  destruct(private_write_after_admit_close cell e namespace_captured admitted Kstop child peer cgroup Int.zero admit_value
    called arguments continuation after_admit final peer event after WRITE PRIVATE CLOSE VALUES ADMIT_CONTINUE)
    as[admit_result[close_result[close_count[close_events[after_close[closed
      [ADMIT_TYPE[ORDER_CLOSE[CLOSE_RUN[CLOSE_CONTINUE PREFIX_CLOSE]]]]]]]]]].
  subst admit_value.
  pose(namespace_admitted:=namespace_checked_admit_env namespace_captured child cgroup admit_result).
  pose(namespace_closed:=namespace_checked_cgroup_close_env namespace_admitted cgroup close_result).
  destruct(private_write_after_close_result cell e namespace_admitted closed Kstop cgroup close_result temporary
    called arguments continuation after_close final peer event after WRITE PRIVATE CGROUP RESULT TEMPORARY CLOSE_CONTINUE)
    as[before_result[result_events[after_result[forgotten[result[constructed
      [ORDER_RESULT[PURE_RESULT[FORGET[RESULT_RUN[RESULT_CONTINUE PREFIX_RESULT]]]]]]]]]]].
  destruct(private_write_after_result_clock cell e namespace_closed constructed Kstop temporary admission result
    called arguments continuation after_result final peer event after WRITE PRIVATE TEMPORARY ADMISSION CLOCK RESULT_CONTINUE)
    as[before_clock[clock_events[after_clock[copied[clock_value[clocked
      [ORDER_CLOCK[PURE_CLOCK[COPY[CLOCK_RUN[CLOCK_CONTINUE PREFIX_CLOCK]]]]]]]]]]].
  assert(ADMITTED_TLS:Mem.valid_block admitted(tls_block cell)).
  { eapply(namespace_steps_tls_valid namespace_ge cell _ _ _ ADMIT_RUN TLS). }
  assert(CLOSED_TLS:Mem.valid_block closed(tls_block cell)).
  { eapply(namespace_steps_tls_valid namespace_ge cell _ _ _ CLOSE_RUN ADMITTED_TLS). }
  assert(FORGOTTEN_TLS:Mem.valid_block forgotten(tls_block cell))by(eapply Mem.store_valid_block_1;eassumption).
  assert(CONSTRUCTED_TLS:Mem.valid_block constructed(tls_block cell)).
  { eapply(namespace_steps_tls_valid namespace_ge cell _ _ _ RESULT_RUN FORGOTTEN_TLS). }
  assert(COPIED_TLS:Mem.valid_block copied(tls_block cell))by(eapply source_assign_valid;eassumption).
  destruct(actual_namespace_clock_projects _ _ _ _ _ CLOCK_RUN)as[clock_actual[CLOCK_EVENTS CLOCK_PROCESS]].
  destruct(clock_actual_return_type cell copied clock_actual clock_value clocked COPIED_TLS CLOCK_PROCESS)
    as[milliseconds CLOCK_TYPE];subst clock_value.
  destruct(private_write_after_clock_publication cell e namespace_closed clocked Kstop admission milliseconds
    called arguments continuation after_clock final peer event after WRITE PRIVATE ADMISSION CLOCK_CONTINUE)
    as[before_publication[after_clock_guard[published
      [ORDER_ELAPSED[PURE_ELAPSED[ELAPSED[CLOCK_GUARDED PREFIX_ELAPSED]]]]]]].
  pose(namespace_clocked:=namespace_checked_clock_env namespace_closed milliseconds).
  assert(CAPTURED_BAD:namespace_bad_binary namespace_captured).
  { left;unfold namespace_captured,namespace_launch_env;WriteAll.lookup. }
  assert(ADMITTED_BAD:namespace_bad_binary namespace_admitted)by(apply namespace_admit_bad_binary;exact CAPTURED_BAD).
  assert(CLOSED_BAD:namespace_bad_binary namespace_closed)by(apply namespace_close_bad_binary;exact ADMITTED_BAD).
  assert(CLOCKED_BAD:namespace_bad_binary namespace_clocked)by(apply namespace_clock_bad_binary;exact CLOSED_BAD).
  assert(PUBLICATION_INPUTS:namespace_clocked!_report=Some(Vint report) /\
    namespace_clocked!_sequence=Some(Vlong sequence)).
  { unfold namespace_clocked,namespace_closed,namespace_admitted,namespace_captured,
      namespace_checked_clock_env,namespace_checked_cgroup_close_env,namespace_checked_admit_env.
    destruct(Int64.eq milliseconds Int64.zero);destruct(Int.eq close_result Int.zero);destruct(Int.eq admit_result Int.zero);
      unfold namespace_admission_clock_env,namespace_after_cgroup_close_env,namespace_cgroup_close_env,
        namespace_after_admit_env,namespace_admit_env,namespace_launch_env;split;WriteAll.lookup. }
  destruct PUBLICATION_INPUTS as[REPORT' SEQUENCE'].
  assert(CLOCKED_GOOD:namespace_clocked!_bad=Some(Vint Int.zero)).
  { eapply private_write_publication_requires_good;eassumption. }
  assert(CLOCKED_VALUES:namespace_launch_values namespace_clocked child peer cgroup Int.zero).
  { apply namespace_clock_retains_values,namespace_close_retains_values,namespace_admit_retains_values;exact VALUES. }
  destruct CLOCKED_VALUES as[CHILD'[PEER'[CGROUP' CHECK']]].
  destruct(private_write_after_publication_release cell e namespace_clocked published Kstop admission report sequence
    called arguments continuation after_clock_guard final peer event after REPORT_OTHER WRITE PRIVATE
    CLOCKED_GOOD REPORT' SEQUENCE' SEND ADMISSION CHECK' CLOCK_GUARDED)
    as[publication_call[publication_events[publication_guard[after_publication[publication_result[after_send
      [ORDER_PUBLICATION[PURE_PUBLICATION[PURE_GUARD[PUBLICATION_RUN[PUBLICATION_CONTINUE PREFIX_PUBLICATION]]]]]]]]]]].
  pose(namespace_published:=namespace_checked_publication_env namespace_clocked sequence publication_result).
  assert(PUBLISHED_BAD:namespace_bad_binary namespace_published)by(apply namespace_publication_bad_binary;exact CLOCKED_BAD).
  assert(PUBLISHED_REPORT:namespace_published!_report=Some(Vint report)).
  { unfold namespace_published,namespace_checked_publication_env.
    destruct(Int.eq publication_result Int.zero);unfold namespace_publication_return_env,namespace_publication_call_env;
      WriteAll.lookup. }
  assert(PUBLISHED_VALUES:namespace_launch_values namespace_published child peer cgroup Int.zero).
  { apply namespace_publication_retains_values;repeat split;assumption. }
  destruct PUBLISHED_VALUES as[CHILD''[PEER''[CGROUP'' CHECK'']]].
  destruct(private_write_release_cut cell e namespace_published after_send child peer report after_publication
    called arguments continuation final event after GLOBAL PUBLISHED_BAD PUBLISHED_REPORT REPORT_OTHER
    CHILD'' PEER'' PUBLICATION_CONTINUE WRITE PRIVATE)as[suffix[ORDER_RELEASE[PREFIX_RELEASE RELEASE_TAIL]]].
  pose(prefix:=((((((repeat namespace_source_event 15++admit_events)++
    (repeat namespace_source_event close_count++close_events))++(before_result++result_events))++
    (before_clock++clock_events))++before_publication)++(publication_call++publication_events++publication_guard))++
    repeat namespace_source_event 5).
  assert(WHOLE_EVENTS:events=prefix++suffix).
  { unfold prefix;rewrite ORDER_ADMIT,ORDER_CLOSE,ORDER_RESULT,ORDER_CLOCK,ORDER_ELAPSED,ORDER_PUBLICATION,ORDER_RELEASE.
    repeat rewrite <-app_assoc;reflexivity. }
  assert(PREFIX:namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le before))prefix
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]
      (namespace_release_cont e namespace_published child peer Kstop)after_send))).
  { unfold prefix.
    eapply namespace_steps_append;[|exact PREFIX_RELEASE].
    eapply namespace_steps_append;[|exact PREFIX_PUBLICATION].
    eapply namespace_steps_append;[|exact PREFIX_ELAPSED].
    eapply namespace_steps_append;[|exact PREFIX_CLOCK].
    eapply namespace_steps_append;[|exact PREFIX_RESULT].
    eapply namespace_steps_append;[|exact PREFIX_CLOSE].
    exact PREFIX_ADMIT. }
  destruct(actual_parent_release_authorized cell e le before Kstop childobject pipe child peer cgroup status temporary admission
    report sequence e namespace_published child peer prefix after_send GLOBAL(conj I I)CHILD PIPE STATUS CGROUP PREFLIGHT
    TEMPORARY ADMISSION PID PEER CGFD CHECK BAD REPORT SEQUENCE TLS PREFIX)as[EXACT_CHILD[EXACT_PEER AUTHORIZED]].
  destruct(actual_private_write_inside_release cell e namespace_published child peer after_send report suffix
    called arguments continuation final event after GLOBAL PUBLISHED_REPORT REPORT_OTHER RELEASE_TAIL WRITE PRIVATE)
    as[local[next[LOCAL STEP]]].
  exists prefix,suffix,namespace_published,after_send,local,next;auto.
Qed.

Lemma namespace_steps_at_event ge cell before events after prefix event suffix:
  namespace_steps ge cell before events after ->events=prefix++event::suffix ->
  exists middle next,namespace_steps ge cell before prefix middle /\
    namespace_step ge cell middle event next /\namespace_steps ge cell next suffix after.
Proof.
  revert before events;induction prefix as[|first rest IH];intros before events RUN EVENTS;subst events.
  - inversion RUN;subst;eexists;eexists;split;[constructor|];eauto.
  - cbn in RUN;inversion RUN;subst.
    match goal with REST:namespace_steps ge cell _ (rest++event::suffix)after|-_=>
      destruct(IH _ _ REST eq_refl)as[current[next[PREFIX[STEP TAIL]]]]end.
    exists current,next;split;[econstructor;eassumption|auto].
Qed.

Theorem actual_private_parent_source_occurrence cell e le before childobject pipe child peer cgroup status temporary admission
    report sequence events target ordinal event io:
  caller_env_global e ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->e!_status=Some(status,tint) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  e!__res__6=Some(temporary,result_type) ->e!_admission=Some(admission,result_type) ->
  Mem.load Mint32 before childobject 0=Some(Vint child) ->Mem.load Mint32 before pipe 0=Some(Vint peer) ->
  Mem.load Mint32 before(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 before(namespace_symbol _preflight)0=Some(Vint Int.zero) ->
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  Mem.valid_block before(tls_block cell) ->cgroup<>peer ->report<>peer ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le before))events target ->
  nth_error events ordinal=Some event ->namespace_socket_io event=Some io ->
  operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=peer ->
  exists prefix release_prefix release_temps released local next,
    ordinal=(length prefix+length release_prefix)%nat /\
    (exists tail,events=prefix++release_prefix++event::tail) /\
    namespace_authorized_parent cell before child peer cgroup status temporary admission report sequence prefix /\
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le before))prefix
      (live(Callstate(Internal f_release_child)[Vint child;Vint peer]
        (namespace_release_cont e release_temps child peer Kstop)released)) /\
    namespace_steps namespace_ge cell(live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop released))release_prefix
      (live local) /\namespace_step namespace_ge cell(live local)event next.
Proof.
  intros GLOBAL CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION PID PEER CGFD CHECK BAD REPORT SEQUENCE TLS
    CG_OTHER REPORT_OTHER RUN SELECTED SOCKET WRITING DESCRIPTOR.
  destruct(nth_error_split _ _ SELECTED)as[earlier[later[EVENTS POSITION]]].
  destruct(namespace_steps_at_event _ _ _ _ _ _ _ _ RUN EVENTS)as[middle[following[INITIAL[STEP TAIL]]]].
  destruct(namespace_socket_step_call _ _ _ _ _ _ STEP SOCKET)as[k[memory SAME]];subst middle.
  assert(PRIVATE:private_namespace_write peer event)by(exists io;auto).
  destruct(actual_private_parent_write_authorized cell e le before childobject pipe child peer cgroup status temporary admission
    report sequence earlier _ _ k memory event following GLOBAL CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION
    PID PEER CGFD CHECK BAD REPORT SEQUENCE TLS CG_OTHER REPORT_OTHER INITIAL STEP PRIVATE)
    as[prefix[release_prefix[release_temps[released[local[next[EARLIER[AUTHORIZED[PREFIX[RELEASE WRITE]]]]]]]]]].
  exists prefix,release_prefix,release_temps,released,local,next;split.
  - rewrite <-POSITION,EARLIER,app_length;reflexivity.
  - split;[exists later;rewrite EVENTS,EARLIER,app_assoc;reflexivity|auto].
Qed.

Theorem actual_private_parent_source_grant cell e le before childobject pipe child peer cgroup status temporary admission
    report sequence events target ordinal event io:
  caller_env_global e ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->e!_status=Some(status,tint) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  e!__res__6=Some(temporary,result_type) ->e!_admission=Some(admission,result_type) ->
  Mem.load Mint32 before childobject 0=Some(Vint child) ->Mem.load Mint32 before pipe 0=Some(Vint peer) ->
  Mem.load Mint32 before(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 before(namespace_symbol _preflight)0=Some(Vint Int.zero) ->
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  Mem.valid_block before(tls_block cell) ->cgroup<>peer ->report<>peer ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le before))events target ->
  nth_error events ordinal=Some event ->namespace_socket_io event=Some io ->
  operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=peer ->
  exists prefix release_prefix tail resume_ordinal,
    events=prefix++release_prefix++event::tail /\
    namespace_authorized_parent cell before child peer cgroup status temporary admission report sequence prefix /\
    nth_error events resume_ordinal=Some(namespace_process(ProcessReleaseSafety.release_resume_event child)) /\
    (resume_ordinal<ordinal)%nat /\operation(source_socket_request io)=writing /\
    descriptor(source_socket_request io)=peer /\requested(source_socket_request io)=1 /\
    source_socket_bytes io=[Byte.repr 165].
Proof.
  intros GLOBAL CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION PID PEER CGFD CHECK BAD REPORT SEQUENCE TLS
    CG_OTHER REPORT_OTHER RUN SELECTED SOCKET WRITING DESCRIPTOR.
  destruct(actual_private_parent_source_occurrence cell e le before childobject pipe child peer cgroup status temporary admission
    report sequence events target ordinal event io GLOBAL CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION
    PID PEER CGFD CHECK BAD REPORT SEQUENCE TLS CG_OTHER REPORT_OTHER RUN SELECTED SOCKET WRITING DESCRIPTOR)
    as[prefix[release_prefix[release_temps[released[local[next[POSITION[FULL[AUTHORIZED[PREFIX[RELEASE WRITE]]]]]]]]]]].
  destruct FULL as[tail EVENTS].
  assert(RELEASE_TLS:Mem.valid_block released(tls_block cell)).
  { eapply(namespace_steps_tls_valid namespace_ge cell _ _ _ PREFIX TLS). }
  assert(HELPER:namespace_steps namespace_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop released))(release_prefix++[event])next).
  { eapply namespace_steps_append;[exact RELEASE|econstructor;[exact WRITE|constructor]]. }
  destruct(actual_namespace_release_socket_checked_from_live_tls cell released child peer
    (release_prefix++[event])next release_prefix event[]io RELEASE_TLS HELPER eq_refl SOCKET)
    as[RESUMED[WRITING'[FD[COUNT BYTES]]]].
  apply In_nth_error in RESUMED as[resume_offset RESUME].
  assert(OFFSET:(resume_offset<length release_prefix)%nat).
  { apply nth_error_Some;rewrite RESUME;discriminate. }
  exists prefix,release_prefix,tail,(length prefix+resume_offset)%nat.
  split;[exact EVENTS|]. split;[exact AUTHORIZED|]. split.
  - rewrite EVENTS,nth_error_app2 by lia.
    replace(length prefix+resume_offset-length prefix)%nat with resume_offset by lia.
    rewrite nth_error_app1 by exact OFFSET;exact RESUME.
  - split;[lia|auto].
Qed.
