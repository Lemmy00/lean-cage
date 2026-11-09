(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Assemble actual useful callbacks through the maintained parent source. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess CallContexts WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessMemory.
From EntryReporting Require Import ResultLayout.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller NamespaceRelease
  NamespaceReporting NamespacePublication NamespaceContexts NamespaceAdmission NamespaceParentSafety NamespaceTLS.
Import ListNotations.
Open Scope Z_scope.

Theorem namespace_plug_actual_steps ge cell before events after suffix:
  is_call_cont suffix ->namespace_steps ge cell before events after ->
  namespace_steps ge cell(plug_machine before suffix)events(plug_machine after suffix).
Proof.
  intros CALL RUN;induction RUN as[state|before event middle rest after STEP RUN IH].
  - apply namespace_steps_nil.
  - eapply namespace_steps_cons;[eapply plug_namespace_step;eassumption|exact IH].
Qed.

From EntryNative Require Import NativeHandoffInput NativeHandoffArguments NativeHandoffInitial.
From EntryProcess Require Import ProcessPaths ProcessAdmissionWitness ProcessClockMemory ProcessClockRun.
From EntryProcess Require Import ProcessPhysicalWitness ProcessPlacement ProcessAllocation.
From EntryReporting Require Import ResultSource ResultSafety ResultOwnership FrameCopy SenderProgram
  SenderSuccessfulRuns SenderSource SenderSelectors SenderReportMemory.
From EntryNamespace Require Import NamespaceParentFrame NamespaceParentData NamespaceParentClock.
Require Import ErrorNumber Library ProcessEffects FrameRecord FrameAllocation DecoderValidity.

Record namespace_useful_callback_input cell e le memory childobject pipe status temporary admission
    run uid report sequence:Prop:={
  namespace_useful_globals:caller_env_global e;
  namespace_useful_global_cells:e!_admission_cgroup=None /\e!_preflight=None;
  namespace_useful_locals:e!_child=Some(childobject,tint) /\e!_pipefd=Some(pipe,tarray tint 2) /\
    e!_status=Some(status,tint) /\e!__res__6=Some(temporary,result_type) /\e!_admission=Some(admission,result_type);
  namespace_useful_temps:le!_bad=Some(Vint Int.zero) /\le!_report=Some(Vint report) /\le!_sequence=Some(Vlong sequence);
  namespace_useful_captures:Mem.load Mint32 memory childobject 0=Some(Vint(Int.repr 2)) /\
    Mem.load Mint32 memory pipe 0=Some(Vint(Int.repr 9)) /\
    Mem.load Mint32 memory(namespace_symbol _admission_cgroup)0=Some(Vint(Int.repr 7)) /\
    Mem.load Mint32 memory(namespace_symbol _preflight)0=Some(Vint Int.zero);
  namespace_useful_errno:entry_errno_ready cell memory;
  namespace_useful_status:Mem.valid_access memory Mint32 status 0 Writable;
  namespace_useful_cgroup:Mem.valid_access memory Mint32(namespace_symbol _admission_cgroup)0 Writable;
  namespace_useful_temporary:Mem.range_perm memory temporary 0 144 Cur Freeable;
  namespace_useful_admission:Mem.range_perm memory admission 0 144 Cur Freeable;
  namespace_useful_separate:status<>tls_block cell /\temporary<>tls_block cell /\
    admission<>tls_block cell /\temporary<>admission /\namespace_symbol _admission_cgroup<>tls_block cell;
  namespace_useful_constants:namespace_parent_constants memory run uid;
  namespace_useful_constants_separate:forall object,namespace_constant_object object ->
    object<>status /\object<>tls_block cell /\object<>namespace_symbol _admission_cgroup /\
      object<>temporary /\object<>admission
}.

Definition namespace_useful_admitted_env le:=
  namespace_checked_admit_env(namespace_launch_env le(Int.repr 2)(Int.repr 9)(Int.repr 7)Int.zero)
    (Int.repr 2)(Int.repr 7)Int.zero.
Definition namespace_useful_closed_env le:=
  namespace_checked_cgroup_close_env(namespace_useful_admitted_env le)(Int.repr 7)Int.zero.
Definition namespace_useful_clock_env le:=
  namespace_checked_clock_env(namespace_useful_closed_env le)(Int64.repr 1000).
Definition namespace_useful_published_env le sequence:=
  namespace_checked_publication_env(namespace_useful_clock_env le)sequence Int.zero.

Lemma namespace_useful_call_global e id:
  caller_env_global e ->caller_global_id id=true ->e!id=None.
Proof. auto. Qed.

Lemma namespace_library_steps ge cell before events after:
  library_steps ge cell before events after ->
  namespace_steps ge cell before(map(fun event=>namespace_process(process_entry(entry_library event)))events)after.
Proof. intro RUN;induction RUN;cbn;[constructor|]. econstructor;[apply namespace_process_step,process_entry_step,entry_library_step;exact H|exact IHRUN]. Qed.

Lemma namespace_errno_store cell before object chunk offset value after:
  object<>tls_block cell ->entry_errno_ready cell before ->
  Mem.store chunk before object offset value=Some after ->entry_errno_ready cell after.
Proof.
  intros DIFFERENT[error[LOW[HIGH[ACCESS LOAD]]]]STORE;exists error;unfold initialized_errno.
  split;[exact LOW|]. split;[exact HIGH|]. split.
  - eapply Mem.store_valid_access_1;eassumption.
  - erewrite Mem.load_store_other;[exact LOAD|exact STORE|left;congruence].
Qed.

Lemma namespace_errno_unchanged cell before after:
  entry_errno_ready cell before ->
  Mem.unchanged_on(fun object _=>object=tls_block cell)before after ->entry_errno_ready cell after.
Proof.
  intros[error[LOW[HIGH[[RANGE ALIGN]LOAD]]]]FRAME;exists error;unfold initialized_errno.
  split;[exact LOW|]. split;[exact HIGH|]. split.
  - split;[intros position BOUND;eapply Mem.perm_unchanged_on;
      [exact FRAME|reflexivity|apply RANGE;exact BOUND]|exact ALIGN].
  - eapply Mem.load_unchanged_on;[exact FRAME|intros;reflexivity|exact LOAD].
Qed.

Theorem namespace_first_path_useful ge cell leaf count start:
  namespace_first_call_path ge leaf count start ->
  exists endpoint,leaf endpoint /\namespace_steps ge cell(live start)(repeat namespace_source_event count)(live endpoint).
Proof.
  intro PATH;induction PATH as[state LEAF|count state next NOTCALL EDGE PATH[endpoint[LEAF RUN]]].
  - exists state;split;[exact LEAF|constructor].
  - exists endpoint;split;[exact LEAF|]. cbn;econstructor;[|exact RUN].
    apply namespace_process_step,process_entry_step,entry_library_step,LibraryMachine.original_step,internal.
    + exact(proj1 EDGE).
    + exact(proj1(proj2 EDGE)).
Qed.

Lemma namespace_useful_retained le child peer cgroup:
  namespace_launch_values
    (namespace_checked_clock_env(namespace_checked_cgroup_close_env
      (namespace_checked_admit_env(namespace_launch_env le child peer cgroup Int.zero)child cgroup Int.zero)
      cgroup Int.zero)(Int64.repr 1000))child peer cgroup Int.zero.
Proof. apply namespace_clock_retains_values,namespace_close_retains_values,namespace_admit_retains_values,namespace_launch_values_set. Qed.

Lemma namespace_useful_inputs le child peer cgroup report sequence:
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  let current:=namespace_checked_clock_env(namespace_checked_cgroup_close_env
      (namespace_checked_admit_env(namespace_launch_env le child peer cgroup Int.zero)child cgroup Int.zero)
      cgroup Int.zero)(Int64.repr 1000)in
  current!_bad=Some(Vint Int.zero) /\current!_report=Some(Vint report) /\current!_sequence=Some(Vlong sequence).
Proof.
  intros BAD REPORT SEQUENCE;unfold namespace_checked_clock_env,namespace_checked_cgroup_close_env,
    namespace_checked_admit_env;change(Int64.eq(Int64.repr 1000)Int64.zero)with false;repeat rewrite Int.eq_true.
  unfold namespace_admission_clock_env,namespace_after_cgroup_close_env,namespace_cgroup_close_env,
    namespace_after_admit_env,namespace_admit_env,namespace_launch_env;repeat split;WriteAll.lookup.
Qed.

Lemma namespace_path_final ge P start count last:
  store_path ge P start count last ->P(memory_of last).
Proof. intro PATH;induction PATH;assumption. Qed.

Definition namespace_quiet_trace(counts:list nat):=flat_map(repeat namespace_source_event)counts.
Definition namespace_reporting_event event:=namespace_process(process_entry(entry_library event)).

Record NamespaceCallbackShape cell before status admission report sequence events:Type:={
  callback_admit_locals:AdmissionLocals;
  callback_admit_first:nat;
  callback_admit_second:nat;
  callback_admitted:mem;
  callback_initial_error:int;
  callback_initial_errno:initialized_errno cell before callback_initial_error;
  callback_status_access:Mem.valid_access before Mint32 status 0 Writable;
  callback_status_tls:status<>tls_block cell;
  callback_admit_source:process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint(Int.repr 2);Vint(Int.repr 7);Vptr status Ptrofs.zero]Kstop before))
    (physical_admission_events cell callback_admit_locals(Int.repr 7)status callback_admit_first callback_admit_second)
    (live(Returnstate(Vint Int.zero)Kstop callback_admitted));
  callback_admitted_errno:initialized_errno cell callback_admitted callback_initial_error;
  callback_admit_frame:Mem.unchanged_on(admission_old_locations cell before status)before callback_admitted;
  callback_admit_permissions:forall object position kind permission,Mem.perm before object position kind permission ->
    Mem.perm callback_admitted object position kind permission;
  callback_clock_before:mem;
  callback_clock_after:mem;
  callback_clock_events:list process_event;
  callback_clock_ready:entry_errno_ready cell callback_clock_before;
  callback_clock_source:process_steps admission_ge cell
    (live(Callstate(Internal f_now_ms)[]Kstop callback_clock_before))callback_clock_events
    (live(Returnstate(Vlong(Int64.repr 1000))Kstop callback_clock_after));
  callback_sender_before:mem;
  callback_sender_after:mem;
  callback_sender_events:list library_event;
  callback_sender_source:library_steps result_ge cell
    (live(sender_initial report sequence admission 0 Kstop callback_sender_before))callback_sender_events
    (live(Returnstate(Vint Int.zero)Kstop callback_sender_after));
  callback_quiet_before_admit:list nat;
  callback_quiet_before_close:list nat;
  callback_quiet_before_clock:list nat;
  callback_quiet_before_sender:list nat;
  callback_quiet_after_sender:list nat;
  callback_event_order:events=
    namespace_quiet_trace callback_quiet_before_admit++
    map namespace_process(physical_admission_events cell callback_admit_locals(Int.repr 7)status callback_admit_first callback_admit_second)++
    namespace_quiet_trace callback_quiet_before_close++[namespace_close_event(Int.repr 7)(close_ok None)]++
    namespace_quiet_trace callback_quiet_before_clock++map namespace_process callback_clock_events++
    namespace_quiet_trace callback_quiet_before_sender++map namespace_reporting_event callback_sender_events++
    namespace_quiet_trace callback_quiet_after_sender
}.

Theorem namespace_useful_callbacks_reach_release_shaped cell e le memory childobject pipe status temporary admission
    run uid report sequence(post:mem->Prop)
    (sender:forall before,
      sender_input cell before admission 0(namespace_admitted_record run uid(Int64.repr 1000))
        (repeat Byte.zero 32)(handoff_global_address ___stringlit_1)handoff_normal_bytes
        (fun tag=>handoff_symbol(report_literal tag)) ->entry_errno_ready cell before ->
      exists events after,library_steps result_ge cell(live(sender_initial report sequence admission 0 Kstop before))events
        (live(Returnstate(Vint Int.zero)Kstop after)) /\post after):
  namespace_useful_callback_input cell e le memory childobject pipe status temporary admission run uid report sequence ->
  exists events final,
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le memory))events
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)final)) /\post final /\inhabited(NamespaceCallbackShape cell memory status admission report sequence events).
Proof.
  intros[GLOBAL[CGGLOBAL CHECKGLOBAL][CHILD[PIPE[STATUS[TEMPORARY ADMISSION]]]][BAD[REPORT SEQUENCE]]
    [PID[PEER[CGROUP CHECK]]]ERRNO STATUS_ACCESS CG_ACCESS TEMP_FREE ADMISSION_FREE
    [STATUS_TLS[TEMP_TLS[ADMISSION_TLS[TEMP_ADMISSION CG_TLS]]]]CONSTANTS CONSTANT_SEPARATE].
  pose proof ERRNO as READY;destruct ERRNO as[initial_error ERRNO].
  assert(CALLEE:forall id,caller_global_id id=true ->e!id=None)by exact GLOBAL.
  assert(ADMIT:e!_admit_child=None)by(apply CALLEE;vm_compute;reflexivity).
  assert(CLOSE:e!_close=None)by(apply CALLEE;vm_compute;reflexivity).
  assert(RESULT:e!_result_of=None)by(apply CALLEE;vm_compute;reflexivity).
  assert(CLOCK:e!_now_ms=None)by(apply CALLEE;vm_compute;reflexivity).
  assert(SEND:e!_send_frame=None)by(apply CALLEE;vm_compute;reflexivity).
  assert(RELEASE:e!_release_child=None)by(apply CALLEE;vm_compute;reflexivity).
  set(captured:=namespace_launch_env le(Int.repr 2)(Int.repr 9)(Int.repr 7)Int.zero).
  pose proof(namespace_launch_capture_source e le memory Kstop childobject pipe(Int.repr 2)(Int.repr 9)(Int.repr 7)Int.zero
    CHILD PIPE CGGLOBAL CHECKGLOBAL PID PEER CGROUP CHECK)as CAPTURE.
  pose proof(namespace_admit_call_source e captured memory Kstop(Int.repr 2)(Int.repr 7)status
    ADMIT STATUS ltac:(unfold captured,namespace_launch_env;WriteAll.lookup)
    ltac:(unfold captured,namespace_launch_env;WriteAll.lookup))as ADMIT_CALL.
  destruct(admission_useful_source_execution_owned cell memory(Int.repr 7)status initial_error ERRNO STATUS_ACCESS STATUS_TLS)
    as[locals[first[second[admitted[ADMIT_RUN[ADMIT_ERRNO[ADMIT_FRAME ADMIT_PERMS]]]]]]].
  assert(ADMITTED_CONSTANTS:namespace_parent_constants admitted run uid).
  { eapply namespace_constants_preserved;[exact CONSTANTS|].
    eapply Mem.unchanged_on_implies;[exact ADMIT_FRAME|].
    intros object position MEMBER VALID;split;[eapply namespace_constants_valid;eassumption|].
    destruct(CONSTANT_SEPARATE object MEMBER)as[NE[TLS REST]];auto. }
  assert(ADMITTED_READY:entry_errno_ready cell admitted)by(exists initial_error;exact ADMIT_ERRNO).
  destruct(namespace_admit_return_source e captured admitted Kstop(Int.repr 2)(Int.repr 7)Int.zero)
    as[admit_return_count ADMIT_RETURN].
  destruct(namespace_cgroup_close_call_source e(namespace_useful_admitted_env le)admitted Kstop(Int.repr 7)
    CLOSE ltac:(unfold namespace_useful_admitted_env,namespace_checked_admit_env,namespace_after_admit_env,
      namespace_admit_env,namespace_launch_env;rewrite Int.eq_true;WriteAll.lookup))as[close_call_count CLOSE_CALL].
  assert(CLOSE_EFFECT:close_effect cell admitted(close_ok None)admitted).
  { split;[apply entry_errno_ready_tls;exact ADMITTED_READY|constructor]. }
  destruct(namespace_cgroup_close_return_source e(namespace_useful_admitted_env le)admitted Kstop(Int.repr 7)Int.zero)
    as[close_return_count CLOSE_RETURN].
  assert(CG_ACCESS':Mem.valid_access admitted Mint32(namespace_symbol _admission_cgroup)0 Writable).
  { destruct CG_ACCESS as[RANGE ALIGN];split;[intros position BOUND;apply ADMIT_PERMS;apply RANGE;exact BOUND|exact ALIGN]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint Int.mone)CG_ACCESS')as[forgotten FORGET_STORE].
  destruct(namespace_cgroup_forget_source e(namespace_useful_closed_env le)admitted forgotten Kstop CGGLOBAL FORGET_STORE)
    as[forget_count FORGET].
  assert(FORGOTTEN_CONSTANTS:namespace_parent_constants forgotten run uid).
  { eapply namespace_constants_preserved;[exact ADMITTED_CONSTANTS|].
    eapply Mem.store_unchanged_on;[exact FORGET_STORE|].
    intros position BOUND MEMBER;destruct(CONSTANT_SEPARATE _ MEMBER)as[_[_[NE REST]]];contradiction. }
  assert(FORGOTTEN_READY:entry_errno_ready cell forgotten).
  { eapply namespace_errno_store;[exact CG_TLS|exact ADMITTED_READY|exact FORGET_STORE]. }
  assert(FORGOTTEN_PERMS:forall object position kind permission,
    Mem.perm memory object position kind permission ->Mem.perm forgotten object position kind permission).
  { intros object position kind permission PERM;eapply Mem.perm_store_1;[exact FORGET_STORE|apply ADMIT_PERMS;exact PERM]. }
  assert(RESULT_INPUT:result_input forgotten temporary 0 run uid).
  { split.
    - split;[lia|]. split;[change(144<=18446744073709551616);lia|]. split;[apply Z.divide_0_r|].
      intros position BOUND;apply FORGOTTEN_PERMS;eapply Mem.perm_implies;[apply TEMP_FREE;exact BOUND|constructor].
    - exists(handoff_symbol _run_id),(handoff_symbol _run_uid);split.
      + unfold result_ge,handoff_ge,handoff_symbol;vm_compute;reflexivity.
      + split;[unfold result_ge,handoff_ge,handoff_symbol;vm_compute;reflexivity|].
        exact(namespace_constant_result _ _ _ FORGOTTEN_CONSTANTS). }
  destruct(namespace_admission_result_call_source e(namespace_useful_closed_env le)forgotten Kstop temporary RESULT TEMPORARY)
    as[result_call_count RESULT_CALL].
  destruct(result_owned_execution forgotten temporary 0(Int.repr 5)Int.zero Int.zero Int.zero uid run Kstop RESULT_INPUT)
    as[constructed[RESULT_PATH[CONTENTS FREED]]].
  pose proof(namespace_path_final _ _ _ _ _ RESULT_PATH)as[RESULT_FRAME RESULT_PERMS];cbn[memory_of]in RESULT_FRAME,RESULT_PERMS.
  assert(CONSTRUCTED_TEMP:Mem.range_perm constructed temporary 0 144 Cur Freeable).
  { intros position BOUND;apply RESULT_PERMS,FORGOTTEN_PERMS;apply TEMP_FREE;exact BOUND. }
  assert(CONSTRUCTED_ADMISSION:Mem.range_perm constructed admission 0 144 Cur Freeable).
  { intros position BOUND;apply RESULT_PERMS,FORGOTTEN_PERMS;apply ADMISSION_FREE;exact BOUND. }
  assert(CONSTRUCTED_READY:entry_errno_ready cell constructed).
  { eapply namespace_errno_unchanged;[exact FORGOTTEN_READY|].
    eapply Mem.unchanged_on_implies;[exact RESULT_FRAME|].
    intros object position SAME VALID;subst object;split;[exact VALID|left;congruence]. }
  assert(CONSTRUCTED_CONSTANTS:namespace_parent_constants constructed run uid).
  { eapply namespace_constants_preserved;[exact FORGOTTEN_CONSTANTS|].
    eapply Mem.unchanged_on_implies;[exact RESULT_FRAME|].
    intros object position MEMBER VALID;split;[exact VALID|].
    left;destruct(CONSTANT_SEPARATE _ MEMBER)as[_[_[_[NE REST]]]];exact NE. }
  assert(CONSTRUCTED_FRAME:frame_result_owned constructed temporary 0(namespace_admitted_record run uid Int64.zero)(repeat Byte.zero 32)).
  { apply namespace_constructed_frame;[intros position BOUND;eapply Mem.perm_implies;
      [apply CONSTRUCTED_TEMP;exact BOUND|constructor]|exact CONTENTS]. }
  destruct(namespace_copy_owned_frame constructed temporary admission _ _ TEMP_ADMISSION CONSTRUCTED_FRAME CONSTRUCTED_ADMISSION)
    as[copied[COPY[COPIED_FRAME[COPIED_FREE COPY_FRAME]]]].
  destruct(namespace_admission_result_return_source e(namespace_useful_closed_env le)constructed copied Kstop temporary admission
    TEMPORARY ADMISSION COPY)as[result_return_count RESULT_RETURN].
  assert(COPIED_CONSTANTS:namespace_parent_constants copied run uid).
  { eapply namespace_constants_preserved;[exact CONSTRUCTED_CONSTANTS|].
    eapply Mem.unchanged_on_implies;[exact COPY_FRAME|].
    intros object position MEMBER VALID;exact(proj2(proj2(proj2(proj2(CONSTANT_SEPARATE _ MEMBER))))). }
  assert(COPIED_READY:entry_errno_ready cell copied).
  { eapply namespace_errno_unchanged;[exact CONSTRUCTED_READY|].
    eapply Mem.unchanged_on_implies;[exact COPY_FRAME|]. intros object position SAME VALID;subst object;congruence. }
  destruct(namespace_admission_clock_call_source e(namespace_useful_closed_env le)copied Kstop CLOCK)
    as[clock_call_count CLOCK_CALL].
  destruct(clock_useful_source_execution cell copied COPIED_READY)as[clock_events[clocked[CLOCK_RUN[CLOCK_FRAME CLOCK_OBSERVATION]]]].
  assert(CLOCKED_FRAME:frame_result_owned clocked admission 0(namespace_admitted_record run uid Int64.zero)(repeat Byte.zero 32)).
  { eapply namespace_frame_unchanged;[exact COPIED_FRAME|].
    eapply Mem.unchanged_on_implies;[exact CLOCK_FRAME|].
    intros object position SAME VALID;subst object;split;[exact VALID|left;exact ADMISSION_TLS]. }
  assert(CLOCKED_FREE:Mem.range_perm clocked admission 0 144 Cur Freeable).
  { intros position BOUND;eapply Mem.perm_unchanged_on;[exact CLOCK_FRAME| |apply COPIED_FREE;exact BOUND].
    split;[eapply Mem.perm_valid_block;apply COPIED_FREE;exact BOUND|left;exact ADMISSION_TLS]. }
  assert(CLOCKED_CONSTANTS:namespace_parent_constants clocked run uid).
  { eapply namespace_constants_preserved;[exact COPIED_CONSTANTS|].
    eapply Mem.unchanged_on_implies;[exact CLOCK_FRAME|].
    intros object position MEMBER VALID;split;[exact VALID|left;exact(proj1(proj2(CONSTANT_SEPARATE _ MEMBER)))]. }
  assert(CLOCKED_READY:entry_errno_ready cell clocked).
  { eapply namespace_clock_actual_ready;[|exact CLOCK_RUN].
    destruct COPIED_READY as[error[LOW[HIGH[ACCESS LOAD]]]].
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(ELAPSED_ACCESS:Mem.valid_access clocked Mint64 admission 72 Writable).
  { split;[intros position BOUND;eapply Mem.perm_implies;[apply CLOCKED_FREE;cbn in BOUND;lia|constructor]|exists 9;reflexivity]. }
  destruct(Mem.valid_access_store _ _ _ _(Vlong(Int64.repr 1000))ELAPSED_ACCESS)as[elapsed ELAPSED_STORE].
  pose proof(namespace_store_elapsed _ _ _ _ _ _ _ CLOCKED_FRAME ELAPSED_STORE)as ELAPSED_FRAME.
  assert(ELAPSED_CONSTANTS:namespace_parent_constants elapsed run uid).
  { eapply namespace_constants_preserved;[exact CLOCKED_CONSTANTS|].
    eapply Mem.store_unchanged_on;[exact ELAPSED_STORE|].
    intros position BOUND MEMBER;exact((proj2(proj2(proj2(proj2(CONSTANT_SEPARATE _ MEMBER)))))eq_refl). }
  assert(ELAPSED_READY:entry_errno_ready cell elapsed).
  { eapply namespace_errno_store;[exact ADMISSION_TLS|exact CLOCKED_READY|exact ELAPSED_STORE]. }
  destruct(namespace_admission_clock_return_source e(namespace_useful_closed_env le)clocked elapsed Kstop admission(Int64.repr 1000)
    ADMISSION ELAPSED_STORE)as[clock_return_count CLOCK_RETURN].
  destruct(namespace_useful_inputs le(Int.repr 2)(Int.repr 9)(Int.repr 7)report sequence BAD REPORT SEQUENCE)
    as[ELAPSED_BAD[ELAPSED_REPORT ELAPSED_SEQUENCE]].
  pose proof(namespace_useful_retained le(Int.repr 2)(Int.repr 9)(Int.repr 7))as RETAINED.
  destruct RETAINED as[RETAIN_CHILD[RETAIN_PEER[RETAIN_CGROUP RETAIN_CHECK]]].
  destruct(namespace_normal_publication_call_source e(namespace_useful_clock_env le)elapsed Kstop admission report sequence
    ELAPSED_BAD ELAPSED_REPORT ELAPSED_SEQUENCE SEND ADMISSION RETAIN_CHECK)as[publication_count PUBLICATION].
  assert(SENDER_INPUT:sender_input cell elapsed admission 0(namespace_admitted_record run uid(Int64.repr 1000))
    (repeat Byte.zero 32)(handoff_global_address ___stringlit_1)handoff_normal_bytes
    (fun tag=>handoff_symbol(report_literal tag))).
  { split;[exact ELAPSED_FRAME|]. split.
    - apply namespace_constants_selectors with(run:=run)(uid:=uid);[exact ELAPSED_CONSTANTS|exact ELAPSED_READY|].
      intros object MEMBER;exact(proj1(proj2(CONSTANT_SEPARATE _ MEMBER))).
    - exists(handoff_symbol ___stringlit_2);split.
      + unfold result_ge,handoff_ge,handoff_symbol;vm_compute;reflexivity.
      + exact(namespace_constant_magic _ _ _ ELAPSED_CONSTANTS). }
  destruct(sender elapsed SENDER_INPUT ELAPSED_READY)as[sender_events[final[SENDER_RUN SENDER_POST]]].
  destruct(namespace_publication_return_source e(namespace_useful_clock_env le)final Kstop sequence Int.zero)
    as[publication_return_count PUBLICATION_RETURN].
  assert(FINAL_BAD:(namespace_useful_published_env le sequence)!_bad=Some(Vint Int.zero)).
  { unfold namespace_useful_published_env,namespace_checked_publication_env;rewrite Int.eq_true.
    unfold namespace_publication_return_env,namespace_publication_call_env;WriteAll.lookup. }
  assert(FINAL_CHILD:(namespace_useful_published_env le sequence)!_launch_child=Some(Vint(Int.repr 2))).
  { unfold namespace_useful_published_env,namespace_checked_publication_env;rewrite Int.eq_true.
    unfold namespace_publication_return_env,namespace_publication_call_env;WriteAll.lookup. }
  assert(FINAL_PEER:(namespace_useful_published_env le sequence)!_launch_peer=Some(Vint(Int.repr 9))).
  { unfold namespace_useful_published_env,namespace_checked_publication_env;rewrite Int.eq_true.
    unfold namespace_publication_return_env,namespace_publication_call_env;WriteAll.lookup. }
  destruct(namespace_authorized_release_call_source e(namespace_useful_published_env le sequence)final Kstop(Int.repr 2)(Int.repr 9)
    FINAL_BAD RELEASE FINAL_CHILD FINAL_PEER)as[release_count RELEASE_CALL].
  eexists;exists final;split.
  - eapply namespace_steps_append;[eapply namespace_store_path_actual;exact CAPTURE|].
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact ADMIT_CALL|].
    eapply namespace_steps_append;[|].
    { pose proof(namespace_process_steps_preserved _ _ _ _ _ ADMIT_RUN)as LIFTED.
      exact(namespace_plug_actual_steps _ _ _ _ _ (namespace_admit_cont e captured(Int.repr 2)(Int.repr 7)Kstop)
        ltac:(cbn;exact I)LIFTED). }
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact ADMIT_RETURN|].
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact CLOSE_CALL|].
    eapply namespace_steps_cons.
    { apply namespace_process_step,process_entry_step,entry_library_step,close_step;exact CLOSE_EFFECT. }
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact CLOSE_RETURN|].
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact FORGET|].
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact RESULT_CALL|].
    eapply namespace_steps_append.
    { pose proof(namespace_store_path_actual _ cell _ _ _ _ RESULT_PATH)as LIFTED.
      exact(namespace_plug_actual_steps _ _ _ _ _
        (namespace_admission_result_cont e(namespace_useful_closed_env le)Kstop)ltac:(cbn;exact I)LIFTED). }
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact RESULT_RETURN|].
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact CLOCK_CALL|].
    eapply namespace_steps_append.
    { pose proof(namespace_process_steps_preserved _ _ _ _ _ CLOCK_RUN)as LIFTED.
      exact(namespace_plug_actual_steps _ _ _ _ _
        (namespace_admission_clock_cont e(namespace_useful_closed_env le)Kstop)ltac:(cbn;exact I)LIFTED). }
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact CLOCK_RETURN|].
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact PUBLICATION|].
    eapply namespace_steps_append.
    { pose proof(namespace_library_steps _ _ _ _ _ SENDER_RUN)as LIFTED.
      exact(namespace_plug_actual_steps _ _ _ _ _
        (namespace_publication_cont e(namespace_useful_clock_env le)sequence Kstop)ltac:(cbn;exact I)LIFTED). }
    eapply namespace_steps_append;[eapply namespace_store_path_actual;exact PUBLICATION_RETURN|].
    eapply namespace_store_path_actual;exact RELEASE_CALL.
  - split;[exact SENDER_POST|]. constructor.
    refine{|callback_admit_locals:=locals;callback_admit_first:=first;callback_admit_second:=second;
      callback_admitted:=admitted;callback_initial_error:=initial_error;callback_initial_errno:=ERRNO;
      callback_status_access:=STATUS_ACCESS;callback_status_tls:=STATUS_TLS;callback_admit_source:=ADMIT_RUN;
      callback_admitted_errno:=ADMIT_ERRNO;callback_admit_frame:=ADMIT_FRAME;callback_admit_permissions:=ADMIT_PERMS;
      callback_clock_before:=copied;callback_clock_after:=clocked;callback_clock_events:=clock_events;
      callback_clock_ready:=COPIED_READY;
      callback_clock_source:=CLOCK_RUN;callback_sender_before:=elapsed;callback_sender_after:=final;
      callback_sender_events:=sender_events;callback_sender_source:=SENDER_RUN;
      callback_quiet_before_admit:=[12%nat;3%nat];
      callback_quiet_before_close:=[admit_return_count;close_call_count];
      callback_quiet_before_clock:=[close_return_count;forget_count;result_call_count;161%nat;
        result_return_count;clock_call_count];
      callback_quiet_before_sender:=[clock_return_count;publication_count];
      callback_quiet_after_sender:=[publication_return_count;release_count]|}.
    cbn[namespace_quiet_trace flat_map];repeat rewrite app_nil_r;repeat rewrite <-app_assoc;reflexivity.
Qed.

Theorem namespace_useful_callbacks_reach_release_with cell e le memory childobject pipe status temporary admission
    run uid report sequence(post:mem->Prop)
    (sender:forall before,
      sender_input cell before admission 0(namespace_admitted_record run uid(Int64.repr 1000))
        (repeat Byte.zero 32)(handoff_global_address ___stringlit_1)handoff_normal_bytes
        (fun tag=>handoff_symbol(report_literal tag)) ->entry_errno_ready cell before ->
      exists events after,library_steps result_ge cell(live(sender_initial report sequence admission 0 Kstop before))events
        (live(Returnstate(Vint Int.zero)Kstop after)) /\post after):
  namespace_useful_callback_input cell e le memory childobject pipe status temporary admission run uid report sequence ->
  exists events final,
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le memory))events
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)final)) /\post final.
Proof.
  intro INPUT.
  destruct(namespace_useful_callbacks_reach_release_shaped cell e le memory childobject pipe status temporary admission
    run uid report sequence post sender INPUT)as[events[final[RUN[POST SHAPE]]]].
  exists events,final;split;assumption.
Qed.

Theorem namespace_useful_callbacks_reach_release cell e le memory childobject pipe status temporary admission
    run uid report sequence:
  namespace_useful_callback_input cell e le memory childobject pipe status temporary admission run uid report sequence ->
  exists events final,
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le memory))events
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)final)).
Proof.
  intro INPUT.
  assert(SENDER:forall before,
    sender_input cell before admission 0(namespace_admitted_record run uid(Int64.repr 1000))
      (repeat Byte.zero 32)(handoff_global_address ___stringlit_1)handoff_normal_bytes
      (fun tag=>handoff_symbol(report_literal tag)) ->entry_errno_ready cell before ->
    exists events after,library_steps result_ge cell(live(sender_initial report sequence admission 0 Kstop before))events
      (live(Returnstate(Vint Int.zero)Kstop after)) /\True).
  { intros before OWN READY;destruct(sender_complete_report_exists cell before report sequence admission 0 _ _ _ _ _ OWN)
      as[events[after[RUN REST]]];exists events,after;split;[exact RUN|exact I]. }
  destruct(namespace_useful_callbacks_reach_release_with cell e le memory childobject pipe status temporary admission
    run uid report sequence(fun _=>True)SENDER INPUT)as[events[after[RUN POST]]].
  exists events,after;exact RUN.
Qed.
