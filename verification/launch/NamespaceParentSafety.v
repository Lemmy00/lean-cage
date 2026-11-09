(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Source guards, callback effects and the private grant share one execution. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess CallContexts WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller ProcessContexts ProcessMemory ProcessClockRun.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller
  NamespaceRelease NamespaceReporting NamespacePublication NamespaceContexts NamespaceAdmission
  NamespaceClosure NamespaceAdmissionProjection NamespaceTLS.
Import ListNotations.
Open Scope Z_scope.

Definition namespace_tail_calls:=
  [_waitpid;_entry_ptrace4;_send_frame;_result_of;_get32;_kill;_read;_close;_fault;_usleep;__exit;
   _put32;_put64;_write_all;_write;_error_number;___errno_location;_memcpy;_strcmp].

Theorem namespace_tail_calls_checked:closure_profile namespace_tail_calls=true.
Proof. vm_compute;reflexivity. Qed.
Theorem namespace_tail_calls_exclude_release:
  closure_forbids_parameters namespace_tail_calls(map fst(fn_params f_release_child))=true.
Proof. vm_compute;reflexivity. Qed.
Theorem namespace_tail_source_checked:closure_statement namespace_tail_calls(namespace_tail 31)=true.
Proof. vm_compute;reflexivity. Qed.

Definition namespace_tail_context k:=caller_cont_global k /\closure_cont namespace_tail_calls k.

Theorem namespace_tail_cannot_release cell e le memory k events arguments continuation final:
  caller_env_global e ->namespace_tail_context k ->
  ~namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 31)k e le memory))events
    (live(Callstate(Internal f_release_child)arguments continuation final)).
Proof.
  intros GLOBAL[GLOBALS CONT].
  change(~namespace_steps caller_ge cell(live(State f_namespace_init(namespace_tail 31)k e le memory))events
    (live(Callstate(Internal f_release_child)arguments continuation final))).
  apply(closure_namespace_cannot_call namespace_tail_calls cell _ events f_release_child arguments continuation final
    namespace_tail_calls_checked namespace_tail_calls_exclude_release).
  split;[split;assumption|split;[exact namespace_tail_source_checked|exact CONT]].
Qed.

Definition namespace_bad_binary le:=le!_bad=Some(Vint Int.zero)\/le!_bad=Some(Vint Int.one).

Lemma namespace_admit_bad_binary le child cgroup returned:
  namespace_bad_binary le ->namespace_bad_binary(namespace_checked_admit_env le child cgroup returned).
Proof.
  unfold namespace_bad_binary,namespace_checked_admit_env.
  destruct(Int.eq returned Int.zero);unfold namespace_after_admit_env,namespace_admit_env;
    [repeat rewrite PTree.gso by discriminate;tauto|rewrite PTree.gss;auto].
Qed.
Lemma namespace_close_bad_binary le cgroup returned:
  namespace_bad_binary le ->namespace_bad_binary(namespace_checked_cgroup_close_env le cgroup returned).
Proof.
  unfold namespace_bad_binary,namespace_checked_cgroup_close_env.
  destruct(Int.eq returned Int.zero);unfold namespace_after_cgroup_close_env,namespace_cgroup_close_env;
    [repeat rewrite PTree.gso by discriminate;tauto|rewrite PTree.gss;auto].
Qed.
Lemma namespace_clock_bad_binary le milliseconds:
  namespace_bad_binary le ->namespace_bad_binary(namespace_checked_clock_env le milliseconds).
Proof.
  unfold namespace_bad_binary,namespace_checked_clock_env.
  destruct(Int64.eq milliseconds Int64.zero);unfold namespace_admission_clock_env;
    [rewrite PTree.gss;auto|repeat rewrite PTree.gso by discriminate;tauto].
Qed.
Lemma namespace_publication_bad_binary le sequence returned:
  namespace_bad_binary le ->namespace_bad_binary(namespace_checked_publication_env le sequence returned).
Proof.
  unfold namespace_bad_binary,namespace_checked_publication_env.
  destruct(Int.eq returned Int.zero);unfold namespace_publication_return_env,namespace_publication_call_env;
    [repeat rewrite PTree.gso by discriminate;tauto|rewrite PTree.gss;auto].
Qed.

Theorem namespace_failed_release_cannot_call cell e le memory k events arguments continuation final:
  caller_env_global e ->namespace_tail_context k ->le!_bad=Some(Vint Int.one) ->
  ~namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 30)k e le memory))events
    (live(Callstate(Internal f_release_child)arguments continuation final)).
Proof.
  intros GLOBAL CONTEXT BAD RUN.
  destruct(namespace_failed_release_frontier e le memory k BAD)as[count[next[NEXT PATH]]].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  exact(namespace_tail_cannot_release _ _ _ _ _ _ _ _ _ GLOBAL CONTEXT TAIL).
Qed.

Theorem namespace_release_requires_good cell e le memory k events arguments continuation final:
  caller_env_global e ->namespace_tail_context k ->namespace_bad_binary le ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 30)k e le memory))events
    (live(Callstate(Internal f_release_child)arguments continuation final)) ->le!_bad=Some(Vint Int.zero).
Proof.
  intros GLOBAL CONTEXT[GOOD|BAD]RUN;[exact GOOD|].
  exfalso;exact(namespace_failed_release_cannot_call _ _ _ _ _ _ _ _ _ GLOBAL CONTEXT BAD RUN).
Qed.

Theorem namespace_publication_requires_good cell e le memory k events arguments continuation final:
  caller_env_global e ->namespace_tail_context k ->namespace_bad_binary le ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 29)k e le memory))events
    (live(Callstate(Internal f_release_child)arguments continuation final)) ->le!_bad=Some(Vint Int.zero).
Proof.
  intros GLOBAL CONTEXT[GOOD|BAD]RUN;[exact GOOD|].
  destruct(namespace_failed_publication_frontier e le memory k BAD)as[count[next[NEXT PATH]]].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  exfalso;exact(namespace_failed_release_cannot_call _ _ _ _ _ _ _ _ _ GLOBAL CONTEXT NEXT TAIL).
Qed.

Theorem namespace_release_body_checked:
  closure_statement namespace_tail_calls(fn_body f_release_child)=true.
Proof. vm_compute;reflexivity. Qed.

Lemma namespace_release_suffix_context e le child peer k:
  caller_env_global e ->namespace_tail_context k ->
  caller_cont_global(namespace_release_cont e le child peer k) /\
    closure_cont namespace_tail_calls(namespace_release_cont e le child peer k).
Proof.
  intros GLOBAL[GLOBALS CONT];split.
  - cbn[namespace_release_cont caller_cont_global];auto.
  - cbn[namespace_release_cont closure_cont]. repeat split;try exact CONT;
      vm_compute;reflexivity.
Qed.

(* The release callback and all remaining parent source have a closed call graph
   excluding another release. This binds any observed grant to the first call. *)
Theorem namespace_release_call_unique cell e le child peer k before arguments continuation final events:
  caller_env_global e ->namespace_tail_context k ->
  namespace_steps namespace_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer](namespace_release_cont e le child peer k)before))events
    (live(Callstate(Internal f_release_child)arguments continuation final)) ->
  events=[] /\arguments=[Vint child;Vint peer] /\continuation=namespace_release_cont e le child peer k /\final=before.
Proof.
  intros GLOBAL CONTEXT RUN;inversion RUN;subst;[auto|].
  destruct(namespace_internal_step_exact namespace_ge cell
    (Callstate(Internal f_release_child)[Vint child;Vint peer](namespace_release_cont e le child peer k)before)
    event middle I H)as[original[EVENT REAL]].
  inversion REAL;subst;cbn in *;try contradiction;try discriminate;
    try match goal with BOUND:boundary _ _ _|-_=>inversion BOUND end.
  - match goal with SOURCE:step2 _ _ _ _|-_=>inversion SOURCE;subst end.
    destruct(namespace_release_suffix_context e le child peer k GLOBAL CONTEXT)as[GLOBALS CONT].
    assert(SAFE:caller_vars_safe f_release_child=true)by(vm_compute;reflexivity).
    match goal with ENTRY:function_entry2 _ _ _ _ _ _ _|-_=>
      pose proof(caller_internal_entry_global _ _ _ _ _ _ SAFE ENTRY)as LOCAL_GLOBAL end.
    exfalso.
    eapply(closure_namespace_cannot_call namespace_tail_calls cell _ _ f_release_child arguments continuation final
      namespace_tail_calls_checked namespace_tail_calls_exclude_release).
    2:eassumption.
    split;[split;[exact LOCAL_GLOBAL|exact GLOBALS]|split;[exact namespace_release_body_checked|exact CONT]].
  - match goal with REST:namespace_steps _ _ (dead _) _ _|-_=>
      destruct(namespace_dead_steps _ _ _ _ _ REST)as[EMPTY IMPOSSIBLE];discriminate end.
Qed.

Theorem namespace_actual_release_call_exact cell e le memory k child peer
    final_env final_temps final_child final_peer events final:
  caller_env_global e ->namespace_tail_context k ->le!_bad=Some(Vint Int.zero) ->e!_release_child=None ->
  le!_launch_child=Some(Vint child) ->le!_launch_peer=Some(Vint peer) ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 30)k e le memory))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
      (namespace_release_cont final_env final_temps final_child final_peer k)final)) ->
  final_child=child /\final_peer=peer /\final=memory /\events=repeat namespace_source_event 5.
Proof.
  intros GLOBAL CONTEXT BAD RELEASE CHILD PEER RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_authorized_release_first_callback e le memory k child peer BAD RELEASE CHILD PEER)RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  destruct(namespace_release_call_unique _ _ _ _ _ _ _ _ _ _ _ GLOBAL CONTEXT TAIL)
    as[EMPTY[ARGUMENTS[CONTINUATION MEMORY]]].
  inversion ARGUMENTS;subst;split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|].
  rewrite app_nil_r;reflexivity.
Qed.

Theorem namespace_tail_calls_no_namespace:
  closure_excludes namespace_tail_calls namespace_primitive_names=true.
Proof. vm_compute;reflexivity. Qed.

Theorem namespace_tail_projects cell e le memory k events target:
  caller_env_global e ->namespace_tail_context k ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 31)k e le memory))events target ->
  exists actual,events=map namespace_process actual /\
    process_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 31)k e le memory))actual target.
Proof.
  intros GLOBAL[GLOBALS CONT]RUN.
  eapply closure_namespace_runs_are_process_runs;
    [exact namespace_tail_calls_checked|exact namespace_tail_calls_no_namespace| |exact RUN].
  split;[split;assumption|split;[exact namespace_tail_source_checked|exact CONT]].
Qed.

Theorem namespace_release_entered_closed e le child peer k arguments before local_env local_temps after:
  caller_env_global e ->namespace_tail_context k ->
  function_entry2 namespace_ge f_release_child arguments before local_env local_temps after ->
  closure_state namespace_tail_calls
    (State f_release_child(fn_body f_release_child)(namespace_release_cont e le child peer k)local_env local_temps after).
Proof.
  intros GLOBAL CONTEXT ENTRY.
  destruct(namespace_release_suffix_context e le child peer k GLOBAL CONTEXT)as[GLOBALS CONT].
  assert(SAFE:caller_vars_safe f_release_child=true)by(vm_compute;reflexivity).
  split.
  - split;[eapply caller_internal_entry_global;eassumption|exact GLOBALS].
  - split;[exact namespace_release_body_checked|exact CONT].
Qed.

Theorem namespace_release_entered_projects cell e le child peer k arguments before local_env local_temps after events target:
  caller_env_global e ->namespace_tail_context k ->
  function_entry2 namespace_ge f_release_child arguments before local_env local_temps after ->
  namespace_steps namespace_ge cell
    (live(State f_release_child(fn_body f_release_child)(namespace_release_cont e le child peer k)local_env local_temps after))
    events target ->
  exists actual,events=map namespace_process actual /\process_steps namespace_ge cell
    (live(State f_release_child(fn_body f_release_child)(namespace_release_cont e le child peer k)local_env local_temps after))
    actual target.
Proof.
  intros GLOBAL CONTEXT ENTRY RUN.
  eapply closure_namespace_runs_are_process_runs;
    [exact namespace_tail_calls_checked|exact namespace_tail_calls_no_namespace|
     eapply namespace_release_entered_closed;eassumption|exact RUN].
Qed.

(* Every callback belongs to this one actual parent transcript. Pure source
   intervals retain ordering without treating a whole callback as a primitive. *)
Inductive namespace_authorized_parent cell before child(peer:int)cgroup status temporary admission report sequence:
    list namespace_event->Prop:=
| namespace_parent_authorized:
    forall first_close before_result before_clock before_publication publication_call publication_guard
      admit_events close_events result_events clock_events publication_events
      admitted closed forgotten constructed copied clocked published result milliseconds,
    Forall(fun event=>event=namespace_source_event)first_close ->
    Forall(fun event=>event=namespace_source_event)before_result ->
    Forall(fun event=>event=namespace_source_event)before_clock ->
    Forall(fun event=>event=namespace_source_event)before_publication ->
    Forall(fun event=>event=namespace_source_event)publication_call ->
    Forall(fun event=>event=namespace_source_event)publication_guard ->
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status Ptrofs.zero]Kstop before))admit_events
      (live(Returnstate(Vint Int.zero)Kstop admitted)) ->
    namespace_steps namespace_ge cell(live(Callstate close_definition[Vint cgroup]Kstop admitted))close_events
      (live(Returnstate(Vint Int.zero)Kstop closed)) ->
    Mem.store Mint32 closed(namespace_symbol _admission_cgroup)0(Vint Int.mone)=Some forgotten ->
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_result_of)
        [Vptr temporary Ptrofs.zero;Vint(Int.repr 5);Vint Int.zero;Vint Int.zero;Vint Int.zero]Kstop forgotten))result_events
      (live(Returnstate result Kstop constructed)) ->
    assign_loc namespace_ge EntryReporting.ResultLayout.result_type constructed admission Ptrofs.zero Full
      (Vptr temporary Ptrofs.zero)copied ->
    namespace_steps namespace_ge cell(live(Callstate(Internal f_now_ms)[]Kstop copied))clock_events
      (live(Returnstate(Vlong milliseconds)Kstop clocked)) ->milliseconds<>Int64.zero ->
    Mem.store Mint64 clocked admission 72(Vlong milliseconds)=Some published ->
    (exists after,namespace_steps namespace_ge cell
      (live(Callstate(Internal f_send_frame)[Vint report;Vlong sequence;Vptr admission Ptrofs.zero]Kstop published))publication_events
      (live(Returnstate(Vint Int.zero)Kstop after))) ->
    namespace_authorized_parent cell before child peer cgroup status temporary admission report sequence
      (repeat namespace_source_event 15++admit_events++first_close++close_events++before_result++result_events++
        before_clock++clock_events++before_publication++publication_call++publication_events++publication_guard++
        repeat namespace_source_event 5).

Theorem actual_parent_release_authorized cell e le before k childobject pipe child peer cgroup status temporary admission
    report sequence final_env final_temps final_child final_peer events final:
  caller_env_global e ->namespace_tail_context k ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->e!_status=Some(status,tint) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  e!__res__6=Some(temporary,EntryReporting.ResultLayout.result_type) ->
  e!_admission=Some(admission,EntryReporting.ResultLayout.result_type) ->
  Mem.load Mint32 before childobject 0=Some(Vint child) ->Mem.load Mint32 before pipe 0=Some(Vint peer) ->
  Mem.load Mint32 before(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 before(namespace_symbol _preflight)0=Some(Vint Int.zero) ->
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  Mem.valid_block before(tls_block cell) ->
  namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)k e le before))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
      (namespace_release_cont final_env final_temps final_child final_peer k)final)) ->
  final_child=child /\final_peer=peer /\
    namespace_authorized_parent cell before child peer cgroup status temporary admission report sequence events.
Proof.
  intros GLOBAL CONTEXT CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION PID PEER CGFD CHECK
    BAD REPORT SEQUENCE TLS RUN.
  assert(ADMIT:e!_admit_child=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(CLOSE:e!_close=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(RESULT:e!_result_of=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(CLOCK:e!_now_ms=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(SEND:e!_send_frame=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(RELEASE:e!_release_child=None)by(apply GLOBAL;vm_compute;reflexivity).
  destruct(actual_parent_capture_and_admit cell e le before k childobject pipe child peer cgroup Int.zero status
    final_env final_temps final_child final_peer events final ADMIT STATUS CHILD PIPE CGROUP PREFLIGHT PID PEER CGFD CHECK RUN)
    as[admit_events[after_admit[admit_value[admitted[ORDER_ADMIT[ADMIT_RUN ADMIT_CONTINUE]]]]]].
  pose(namespace_captured:=namespace_launch_env le child peer cgroup Int.zero).
  assert(VALUES:namespace_launch_values namespace_captured child peer cgroup Int.zero)by(apply namespace_launch_values_set).
  destruct(namespace_actual_admit_then_close cell e namespace_captured admitted k child peer cgroup Int.zero admit_value
    final_env final_temps final_child final_peer after_admit final CLOSE VALUES ADMIT_CONTINUE)
    as[admit_result[close_result[close_count[close_events[after_close[closed
      [ADMIT_TYPE[ORDER_CLOSE[CLOSE_RUN CLOSE_CONTINUE]]]]]]]]].
  subst admit_value.
  pose(namespace_admitted:=namespace_checked_admit_env namespace_captured child cgroup admit_result).
  pose(namespace_closed:=namespace_checked_cgroup_close_env namespace_admitted cgroup close_result).
  destruct(namespace_actual_close_then_result cell e namespace_admitted closed k cgroup close_result temporary
    final_env final_temps final_child final_peer after_close final CGROUP RESULT TEMPORARY CLOSE_CONTINUE)
    as[before_result[result_events[after_result[forgotten[result[constructed
      [ORDER_RESULT[PURE_RESULT[FORGET[RESULT_RUN RESULT_CONTINUE]]]]]]]]]].
  destruct(namespace_actual_result_then_clock cell e namespace_closed constructed k temporary admission result
    final_env final_temps final_child final_peer after_result final TEMPORARY ADMISSION CLOCK RESULT_CONTINUE)
    as[before_clock[clock_events[after_clock[copied[clock_value[clocked
      [ORDER_CLOCK[PURE_CLOCK[COPY[CLOCK_RUN CLOCK_CONTINUE]]]]]]]]]].
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
  destruct(namespace_actual_clock_then_publication cell e namespace_closed clocked k admission milliseconds
    final_env final_temps final_child final_peer after_clock final ADMISSION CLOCK_CONTINUE)
    as[before_publication[after_clock_guard[published[ORDER_ELAPSED[PURE_ELAPSED[ELAPSED CLOCK_GUARDED]]]]]].
  pose(namespace_clocked:=namespace_checked_clock_env namespace_closed milliseconds).
  assert(CAPTURED_BAD:namespace_bad_binary namespace_captured).
  { left;unfold namespace_captured,namespace_launch_env;WriteAll.lookup. }
  assert(ADMITTED_BAD:namespace_bad_binary namespace_admitted)by(apply namespace_admit_bad_binary;exact CAPTURED_BAD).
  assert(CLOSED_BAD:namespace_bad_binary namespace_closed)by(apply namespace_close_bad_binary;exact ADMITTED_BAD).
  assert(CLOCKED_BAD:namespace_bad_binary namespace_clocked)by(apply namespace_clock_bad_binary;exact CLOSED_BAD).
  assert(CLOCKED_GOOD:namespace_clocked!_bad=Some(Vint Int.zero)).
  { eapply namespace_publication_requires_good;eassumption. }
  destruct(release_after_clock_requires_nonzero namespace_closed milliseconds CLOCKED_GOOD)as[NONZERO CLOSE_GOOD].
  destruct(successful_close_guard_requires_return_zero namespace_admitted cgroup close_result CLOSE_GOOD)
    as[CLOSE_ZERO ADMIT_GOOD].
  destruct(successful_admit_guard_requires_return_zero namespace_captured child cgroup admit_result ADMIT_GOOD)
    as[ADMIT_ZERO CAPTURE_GOOD].
  assert(PUBLICATION_INPUTS:namespace_clocked!_report=Some(Vint report) /\
    namespace_clocked!_sequence=Some(Vlong sequence)).
  { unfold namespace_clocked,namespace_closed,namespace_admitted,namespace_captured,
      namespace_checked_clock_env,namespace_checked_cgroup_close_env,namespace_checked_admit_env.
    rewrite Int64.eq_false by exact NONZERO;rewrite CLOSE_ZERO,ADMIT_ZERO;repeat rewrite Int.eq_true.
    unfold namespace_admission_clock_env,namespace_after_cgroup_close_env,namespace_cgroup_close_env,
      namespace_after_admit_env,namespace_admit_env,namespace_launch_env;split;WriteAll.lookup. }
  destruct PUBLICATION_INPUTS as[REPORT' SEQUENCE'].
  assert(CLOCKED_VALUES:namespace_launch_values namespace_clocked child peer cgroup Int.zero).
  { apply namespace_clock_retains_values,namespace_close_retains_values,namespace_admit_retains_values;exact VALUES. }
  destruct CLOCKED_VALUES as[CHILD'[PEER'[CGROUP' CHECK']]].
  destruct(namespace_actual_publication_then_release cell e namespace_clocked published k admission report sequence
    final_env final_temps final_child final_peer after_clock_guard final CLOCKED_GOOD REPORT' SEQUENCE'
    SEND ADMISSION CHECK' CLOCK_GUARDED)
    as[publication_call[publication_events[publication_guard[after_publication[publication_result[after_send
      [ORDER_PUBLICATION[PURE_PUBLICATION[PURE_GUARD[PUBLICATION_RUN PUBLICATION_CONTINUE]]]]]]]]]].
  pose(namespace_published:=namespace_checked_publication_env namespace_clocked sequence publication_result).
  assert(PUBLISHED_BAD:namespace_bad_binary namespace_published)by(apply namespace_publication_bad_binary;exact CLOCKED_BAD).
  assert(PUBLISHED_GOOD:namespace_published!_bad=Some(Vint Int.zero)).
  { eapply namespace_release_requires_good;eassumption. }
  destruct(successful_publication_guard_requires_return_zero namespace_clocked sequence publication_result PUBLISHED_GOOD)
    as[PUBLICATION_ZERO CLOCKED_GOOD'].
  assert(PUBLISHED_VALUES:namespace_launch_values namespace_published child peer cgroup Int.zero).
  { apply namespace_publication_retains_values;repeat split;assumption. }
  destruct PUBLISHED_VALUES as[CHILD''[PEER''[CGROUP'' CHECK'']]].
  destruct(namespace_actual_release_call_exact cell e namespace_published after_send k child peer
    final_env final_temps final_child final_peer after_publication final GLOBAL CONTEXT PUBLISHED_GOOD RELEASE
    CHILD'' PEER'' PUBLICATION_CONTINUE)as[CHILD_EXACT[PEER_EXACT[FINAL_MEMORY RELEASE_EVENTS]]].
  split;[exact CHILD_EXACT|]. split;[exact PEER_EXACT|].
  rewrite ORDER_ADMIT,ORDER_CLOSE,ORDER_RESULT,ORDER_CLOCK,ORDER_ELAPSED,ORDER_PUBLICATION,RELEASE_EVENTS.
  repeat rewrite <-app_assoc.
  eapply namespace_parent_authorized with(admitted:=admitted)(closed:=closed)(forgotten:=forgotten)
    (constructed:=constructed)(copied:=copied)(clocked:=clocked)(published:=published)(result:=result)
    (milliseconds:=milliseconds).
  - apply namespace_source_repeat.
  - exact PURE_RESULT.
  - exact PURE_CLOCK.
  - exact PURE_ELAPSED.
  - exact PURE_PUBLICATION.
  - exact PURE_GUARD.
  - rewrite <-ADMIT_ZERO;exact ADMIT_RUN.
  - rewrite <-CLOSE_ZERO;exact CLOSE_RUN.
  - exact FORGET.
  - exact RESULT_RUN.
  - exact COPY.
  - exact CLOCK_RUN.
  - exact NONZERO.
  - exact ELAPSED.
  - exists after_send;rewrite <-PUBLICATION_ZERO;exact PUBLICATION_RUN.
Qed.
