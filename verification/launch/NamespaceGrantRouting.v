(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Recover earlier callbacks from the same observed private write. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess CallContexts WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryReporting Require Import ResultLayout.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller ProcessContexts ProcessMemory ProcessClockRun.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller
  NamespaceRelease NamespaceReporting NamespacePublication NamespaceContexts NamespaceAdmission
  NamespaceClosure NamespaceAdmissionProjection NamespaceTLS NamespaceGrantAuthorization.
Import ListNotations.
Open Scope Z_scope.

Theorem private_write_after_capture_admit cell e le memory k childobject pipe child peer cgroup checking status
    called arguments continuation events after  grant_peer writeEvent writeAfter:
  cgroup<>grant_peer ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation after))writeEvent writeAfter ->
  private_namespace_write grant_peer writeEvent ->
  e!_admit_child=None ->e!_status=Some(status,tint) ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  Mem.load Mint32 memory childobject 0=Some(Vint child) ->
  Mem.load Mint32 memory pipe 0=Some(Vint peer) ->
  Mem.load Mint32 memory(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 memory(namespace_symbol _preflight)0=Some(Vint checking) ->
  namespace_steps namespace_ge cell
    (live(State f_namespace_init(namespace_tail 20)k e le memory))events
    (live(Callstate called arguments continuation after)) ->
  exists callback after_call returned result_memory,
    events=repeat namespace_source_event 15++callback++after_call /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status Ptrofs.zero]Kstop memory))callback
      (live(Returnstate returned Kstop result_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate returned
        (namespace_admit_cont e(namespace_launch_env le child peer cgroup checking)child cgroup k)result_memory))after_call
      (live(Callstate called arguments continuation after)) /\
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)k e le memory))
      (repeat namespace_source_event 15++callback)
      (live(Returnstate returned(namespace_admit_cont e(namespace_launch_env le child peer cgroup checking)child cgroup k)
        result_memory)).
Proof.
  intros OTHER WRITE PRIVATE ADMIT STATUS CHILD PIPE CGROUP PREFLIGHT PID PEER CGFD CHECK RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_captured_admit_first_callback e le memory k childobject pipe child peer cgroup checking status
      ADMIT STATUS CHILD PIPE CGROUP PREFLIGHT PID PEER CGFD CHECK)RUN)
    as[endpoint[remaining[EVENTS[SAME[PREFIX TAIL]]]]].
  subst endpoint.
  destruct(callback_returns_before_private_write namespace_ge cell
    (Internal f_admit_child)[Vint child;Vint cgroup;Vptr status Ptrofs.zero]
    (namespace_admit_cont e(namespace_launch_env le child peer cgroup checking)child cgroup k)memory grant_peer remaining
    called arguments continuation after writeEvent writeAfter
    I (admission_excludes_private _ _ _ _ _ _ OTHER) TAIL WRITE PRIVATE)
    as[callback[rest[returned[result_memory[CALLS[CALLEE CONTINUE]]]]]].
  exists callback,rest,returned,result_memory;split;[rewrite EVENTS,CALLS;reflexivity|].
  split;[exact CALLEE|]. split;[exact CONTINUE|].
  eapply namespace_steps_append;[exact PREFIX|].
  exact(namespace_grant_plug_steps _ _ _ _ _ (namespace_admit_cont e(namespace_launch_env le child peer cgroup checking)child cgroup k) I CALLEE).
Qed.

Theorem private_write_after_admit_close cell e le memory k child peer cgroup checking returned
    called arguments continuation events final grant_peer writeEvent writeAfter:
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))writeEvent writeAfter ->
  private_namespace_write grant_peer writeEvent ->
  e!_close=None ->namespace_launch_values le child peer cgroup checking ->
  namespace_steps namespace_ge cell
    (live(Returnstate returned(namespace_admit_cont e le child cgroup k)memory))events
    (live(Callstate called arguments continuation final)) ->
  exists admit_result close_result count callback suffix after,
    returned=Vint admit_result /\events=repeat namespace_source_event count++callback++suffix /\
    namespace_steps namespace_ge cell
      (live(Callstate close_definition[Vint cgroup]Kstop memory))callback
      (live(Returnstate(Vint close_result)Kstop after)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint close_result)
        (namespace_cgroup_close_cont e(namespace_checked_admit_env le child cgroup admit_result)cgroup k)after))suffix
      (live(Callstate called arguments continuation final)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate returned(namespace_admit_cont e le child cgroup k)memory))
      (repeat namespace_source_event count++callback)
      (live(Returnstate(Vint close_result)
        (namespace_cgroup_close_cont e(namespace_checked_admit_env le child cgroup admit_result)cgroup k)after)).
Proof.
  intros WRITE PRIVATE CLOSE VALUES RUN.
  destruct(namespace_admit_actual_return_type _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)as[admit_result SAME];subst returned.
  destruct(namespace_admit_return_frontier e le memory k child cgroup admit_result)as[count GUARD].
  pose proof(namespace_admit_retains_values le child peer cgroup checking admit_result VALUES)as KEPT.
  destruct KEPT as[CHILD[PEER[CGROUP CHECK]]].
  assert(PATH:namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate close_definition[Vint cgroup]
      (namespace_cgroup_close_cont e(namespace_checked_admit_env le child cgroup admit_result)cgroup k)memory)
    (count+3)
    (Returnstate(Vint admit_result)(namespace_admit_cont e le child cgroup k)memory)).
  { eapply namespace_first_call_bind with(count:=count)(extra:=3%nat)
      (first_leaf:=fun endpoint=>endpoint=State f_namespace_init(namespace_tail 25)k e
        (namespace_checked_admit_env le child cgroup admit_result)memory);[exact GUARD|].
    intros endpoint END;subst endpoint.
    eapply namespace_cgroup_close_first_callback;eassumption. }
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  destruct(callback_returns_before_private_write namespace_ge cell close_definition[Vint cgroup]
    (namespace_cgroup_close_cont e(namespace_checked_admit_env le child cgroup admit_result)cgroup k)memory grant_peer rest
    called arguments continuation final writeEvent writeAfter
    I (close_excludes_private _ _ _ _) TAIL WRITE PRIVATE)
    as[callback[suffix[value[after[ORDER[CALLEE CONTINUE]]]]]].
  destruct(namespace_close_actual_return_type _ _ _ _ _ _ _ _ _ _ _ _ CONTINUE)as[close_result SAME];subst value.
  exists admit_result,close_result,(count+3)%nat,callback,suffix,after.
  split;[reflexivity|]. split;[rewrite EVENTS,ORDER;reflexivity|].
  split;[exact CALLEE|]. split;[exact CONTINUE|].
  eapply namespace_steps_append;[exact PREFIX|].
  exact(namespace_grant_plug_steps _ _ _ _ _ (namespace_cgroup_close_cont e(namespace_checked_admit_env le child cgroup admit_result)cgroup k) I CALLEE).
Qed.

Theorem private_write_after_close_result cell e le memory k cgroup close_result temporary
    called arguments continuation events final grant_peer writeEvent writeAfter:
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))writeEvent writeAfter ->
  private_namespace_write grant_peer writeEvent ->
  e!_admission_cgroup=None ->e!_result_of=None ->e!__res__6=Some(temporary,result_type) ->
  namespace_steps namespace_ge cell
    (live(Returnstate(Vint close_result)(namespace_cgroup_close_cont e le cgroup k)memory))events
    (live(Callstate called arguments continuation final)) ->
  exists prefix callback suffix forgotten result result_memory,
    events=prefix++callback++suffix /\Forall(fun event=>event=namespace_source_event)prefix /\
    Mem.store Mint32 memory(namespace_symbol _admission_cgroup)0(Vint Int.mone)=Some forgotten /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_result_of)
        [Vptr temporary Ptrofs.zero;Vint(Int.repr 5);Vint Int.zero;Vint Int.zero;Vint Int.zero]Kstop forgotten))callback
      (live(Returnstate result Kstop result_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate result(namespace_admission_result_cont e
        (namespace_checked_cgroup_close_env le cgroup close_result)k)result_memory))suffix
      (live(Callstate called arguments continuation final)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint close_result)(namespace_cgroup_close_cont e le cgroup k)memory))(prefix++callback)
      (live(Returnstate result(namespace_admission_result_cont e
        (namespace_checked_cgroup_close_env le cgroup close_result)k)result_memory)).
Proof.
  intros WRITE PRIVATE GLOBAL RESULT TEMPORARY RUN.
  destruct(namespace_cgroup_close_return_frontier e le memory k cgroup close_result)as[count GUARD].
  assert(PATH:namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init namespace_cgroup_forget(Kseq(namespace_tail 27)k)e
      (namespace_checked_cgroup_close_env le cgroup close_result)memory)(count+1)
    (Returnstate(Vint close_result)(namespace_cgroup_close_cont e le cgroup k)memory)).
  { eapply namespace_first_call_bind with(count:=count)(extra:=1%nat)
      (first_leaf:=fun endpoint=>endpoint=State f_namespace_init(namespace_tail 26)k e
        (namespace_checked_cgroup_close_env le cgroup close_result)memory);[exact GUARD|].
    intros endpoint SAME;subst endpoint;apply namespace_cgroup_forget_frontier. }
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  unfold namespace_cgroup_forget in TAIL.
  assert(EXPRESSION:expression_value namespace_ge e
    (namespace_checked_cgroup_close_env le cgroup close_result)memory
    (Eunop Oneg(Econst_int Int.one tint)tint)(Vint Int.mone)).
  { apply old_expression_value;eapply value_unary;[apply value_int|reflexivity]. }
  destruct(namespace_actual_assignment namespace_ge cell f_namespace_init
    (Evar _admission_cgroup tint)(Eunop Oneg(Econst_int Int.one tint)tint)(Kseq(namespace_tail 27)k)e
    (namespace_checked_cgroup_close_env le cgroup close_result)memory(namespace_symbol _admission_cgroup)Ptrofs.zero
    (Vint Int.mone)(Vint Int.mone)rest called arguments continuation final
    (global_location_value _ _ _ _ _ _ _ GLOBAL namespace_admission_symbol)
    EXPRESSION eq_refl TAIL)
    as[forgotten[remaining[ASSIGN_EVENTS[ASSIGN NEXT]]]].
  assert(STORE:Mem.store Mint32 memory(namespace_symbol _admission_cgroup)0(Vint Int.mone)=Some forgotten).
  { inversion ASSIGN;subst;cbn in *;try discriminate.
    match goal with MODE:By_value Mint32=By_value _|-_=>inversion MODE;subst end;assumption. }
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_after_forget_result_frontier e(namespace_checked_cgroup_close_env le cgroup close_result)
      forgotten k temporary RESULT TEMPORARY)NEXT)
    as[endpoint[result_rest[RESULT_EVENTS[SAME[RESULT_PREFIX RESULT_TAIL]]]]];subst endpoint.
  destruct(callback_returns_before_private_write namespace_ge cell(Internal f_result_of)
    [Vptr temporary Ptrofs.zero;Vint(Int.repr 5);Vint Int.zero;Vint Int.zero;Vint Int.zero]
    (namespace_admission_result_cont e(namespace_checked_cgroup_close_env le cgroup close_result)k)forgotten grant_peer result_rest
    called arguments continuation final writeEvent writeAfter
    I (result_excludes_private _ _ _ _) RESULT_TAIL WRITE PRIVATE)
    as[callback[suffix[result[result_memory[ORDER[CALLEE CONTINUE]]]]]].
  exists(repeat namespace_source_event(count+1)++namespace_source_event::repeat namespace_source_event 4),
    callback,suffix,forgotten,result,result_memory.
  split.
  - rewrite EVENTS,ASSIGN_EVENTS,RESULT_EVENTS,ORDER;repeat rewrite <-app_assoc;reflexivity.
  - split;[apply Forall_app;split;[apply namespace_source_repeat|constructor;[reflexivity|apply namespace_source_repeat]]|].
    split;[exact STORE|]. split;[exact CALLEE|]. split;[exact CONTINUE|].
    repeat rewrite <-app_assoc;eapply namespace_steps_append;[exact PREFIX|].
    econstructor.
    + apply namespace_grant_store_step;eapply assignment_source_edge;
        [exact(global_location_value _ _ _ _ _ _ _ GLOBAL namespace_admission_symbol)|
         exact EXPRESSION|reflexivity|exact ASSIGN].
    + eapply namespace_steps_append;[exact RESULT_PREFIX|].
      exact(namespace_grant_plug_steps _ _ _ _ _ (namespace_admission_result_cont e(namespace_checked_cgroup_close_env le cgroup close_result)k) I CALLEE).
Qed.

Theorem private_write_after_result_clock cell e le memory k temporary admission returned
    called arguments continuation events final grant_peer writeEvent writeAfter:
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))writeEvent writeAfter ->
  private_namespace_write grant_peer writeEvent ->
  e!__res__6=Some(temporary,result_type) ->e!_admission=Some(admission,result_type) ->e!_now_ms=None ->
  namespace_steps namespace_ge cell
    (live(Returnstate returned(namespace_admission_result_cont e le k)memory))events
    (live(Callstate called arguments continuation final)) ->
  exists prefix callback suffix copied clock_result clock_memory,
    events=prefix++callback++suffix /\Forall(fun event=>event=namespace_source_event)prefix /\
    assign_loc namespace_ge result_type memory admission Ptrofs.zero Full(Vptr temporary Ptrofs.zero)copied /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_now_ms)[]Kstop copied))callback
      (live(Returnstate clock_result Kstop clock_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate clock_result(namespace_admission_clock_cont e le k)clock_memory))suffix
      (live(Callstate called arguments continuation final)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate returned(namespace_admission_result_cont e le k)memory))(prefix++callback)
      (live(Returnstate clock_result(namespace_admission_clock_cont e le k)clock_memory)).
Proof.
  intros WRITE PRIVATE TEMPORARY ADMISSION CLOCK RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_result_return_copy_frontier e le memory k returned)RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  unfold namespace_admission_copy in TAIL.
  assert(EXPRESSION:expression_value namespace_ge e le memory(Evar __res__6 result_type)(Vptr temporary Ptrofs.zero)).
  { eapply location_read_value;[apply local_location_value;exact TEMPORARY|apply deref_loc_copy;reflexivity]. }
  destruct(namespace_actual_assignment namespace_ge cell f_namespace_init
    (Evar _admission result_type)(Evar __res__6 result_type)(Kseq(namespace_tail 28)k)e le memory
    admission Ptrofs.zero(Vptr temporary Ptrofs.zero)(Vptr temporary Ptrofs.zero)rest
    called arguments continuation final
    (local_location_value _ _ _ _ _ _ _ ADMISSION)
    EXPRESSION eq_refl TAIL)
    as[copied[remaining[ASSIGN_EVENTS[ASSIGN NEXT]]]].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_after_copy_clock_frontier e le copied k CLOCK)NEXT)
    as[endpoint[clock_rest[CLOCK_EVENTS[SAME[CLOCK_PREFIX CLOCK_TAIL]]]]];subst endpoint.
  destruct(callback_returns_before_private_write namespace_ge cell(Internal f_now_ms)[]
    (namespace_admission_clock_cont e le k)copied grant_peer clock_rest
    called arguments continuation final writeEvent writeAfter
    I (clock_excludes_private _ _ _ _) CLOCK_TAIL WRITE PRIVATE)
    as[callback[suffix[clock_result[clock_memory[ORDER[CALLEE CONTINUE]]]]]].
  exists(repeat namespace_source_event 2++namespace_source_event::repeat namespace_source_event 6),
    callback,suffix,copied,clock_result,clock_memory.
  split.
  - rewrite EVENTS,ASSIGN_EVENTS,CLOCK_EVENTS,ORDER;repeat rewrite <-app_assoc;reflexivity.
  - split;[apply Forall_app;split;[apply namespace_source_repeat|constructor;[reflexivity|apply namespace_source_repeat]]|].
    split;[exact ASSIGN|]. split;[exact CALLEE|]. split;[exact CONTINUE|].
    repeat rewrite <-app_assoc;eapply namespace_steps_append;[exact PREFIX|].
    econstructor.
    + apply namespace_grant_store_step;eapply assignment_source_edge;
        [exact(local_location_value _ _ _ _ _ _ _ ADMISSION)|exact EXPRESSION|reflexivity|exact ASSIGN].
    + eapply namespace_steps_append;[exact CLOCK_PREFIX|].
      exact(namespace_grant_plug_steps _ _ _ _ _ (namespace_admission_clock_cont e le k) I CALLEE).
Qed.

Theorem private_write_after_clock_publication cell e le memory k admission milliseconds
    called arguments continuation events final grant_peer writeEvent writeAfter:
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))writeEvent writeAfter ->
  private_namespace_write grant_peer writeEvent ->
  e!_admission=Some(admission,result_type) ->
  namespace_steps namespace_ge cell
    (live(Returnstate(Vlong milliseconds)(namespace_admission_clock_cont e le k)memory))events
    (live(Callstate called arguments continuation final)) ->
  exists prefix suffix stored,
    events=prefix++suffix /\Forall(fun event=>event=namespace_source_event)prefix /\
    Mem.store Mint64 memory admission 72(Vlong milliseconds)=Some stored /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 29)k e(namespace_checked_clock_env le milliseconds)stored))suffix
      (live(Callstate called arguments continuation final)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vlong milliseconds)(namespace_admission_clock_cont e le k)memory))prefix
      (live(State f_namespace_init(namespace_tail 29)k e(namespace_checked_clock_env le milliseconds)stored)).
Proof.
  intros WRITE PRIVATE ADMISSION RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_clock_return_elapsed_frontier e le memory k milliseconds)RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  unfold namespace_admission_elapsed in TAIL.
  assert(LOCATION:location_value namespace_ge e(namespace_admission_clock_env le milliseconds)memory
    (Efield(Evar _admission result_type)_elapsed tulong)admission(Ptrofs.repr 72)).
  { rewrite namespace_reporting_environment.
    eapply current_result_field_location with(offset:=Ptrofs.zero)(delta:=72).
    - eapply location_read_value;[apply local_location_value;exact ADMISSION|apply deref_loc_copy;reflexivity].
    - reflexivity.
    - reflexivity. }
  assert(EXPRESSION:expression_value namespace_ge e(namespace_admission_clock_env le milliseconds)memory
    (Etempvar _t'15 tulong)(Vlong milliseconds)).
  { apply old_expression_value,value_temp;unfold namespace_admission_clock_env;apply PTree.gss. }
  destruct(namespace_actual_assignment namespace_ge cell f_namespace_init
    (Efield(Evar _admission result_type)_elapsed tulong)(Etempvar _t'15 tulong)
    (Kseq namespace_admission_clock_guard(Kseq(namespace_tail 29)k))e
    (namespace_admission_clock_env le milliseconds)memory admission(Ptrofs.repr 72)
    (Vlong milliseconds)(Vlong milliseconds)rest called arguments continuation final LOCATION EXPRESSION eq_refl TAIL)
    as[stored[remaining[ASSIGN_EVENTS[ASSIGN NEXT]]]].
  assert(STORE:Mem.store Mint64 memory admission 72(Vlong milliseconds)=Some stored).
  { inversion ASSIGN;subst;cbn in *;try discriminate.
    match goal with MODE:By_value Mint64=By_value _|-_=>inversion MODE;subst end;assumption. }
  destruct(namespace_after_elapsed_clock_guard e le stored k milliseconds)as[count GUARD].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ GUARD NEXT)
    as[endpoint[suffix[GUARD_EVENTS[SAME[GUARD_PREFIX CONTINUE]]]]];subst endpoint.
  exists(repeat namespace_source_event 4++namespace_source_event::repeat namespace_source_event count),suffix,stored.
  split;[rewrite EVENTS,ASSIGN_EVENTS,GUARD_EVENTS;repeat rewrite <-app_assoc;reflexivity|].
  split;[apply Forall_app;split;[apply namespace_source_repeat|constructor;[reflexivity|apply namespace_source_repeat]]|].
  split;[exact STORE|]. split;[exact CONTINUE|].
  repeat rewrite <-app_assoc;eapply namespace_steps_append;[exact PREFIX|].
  econstructor.
  - apply namespace_grant_store_step;eapply assignment_source_edge;
      [exact LOCATION|exact EXPRESSION|reflexivity|exact ASSIGN].
  - exact GUARD_PREFIX.
Qed.

Theorem private_write_after_publication_release cell e le memory k admission report sequence
    called arguments continuation events final grant_peer writeEvent writeAfter:
  report<>grant_peer ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))writeEvent writeAfter ->
  private_namespace_write grant_peer writeEvent ->
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  e!_send_frame=None ->e!_admission=Some(admission,result_type) ->le!_launch_check=Some(Vint Int.zero) ->
  namespace_steps namespace_ge cell
    (live(State f_namespace_init(namespace_tail 29)k e le memory))events
    (live(Callstate called arguments continuation final)) ->
  exists prefix callback guard suffix returned after,
    events=prefix++callback++guard++suffix /\
    Forall(fun event=>event=namespace_source_event)prefix /\
    Forall(fun event=>event=namespace_source_event)guard /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_send_frame)[Vint report;Vlong sequence;Vptr admission Ptrofs.zero]Kstop memory))callback
      (live(Returnstate(Vint returned)Kstop after)) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 30)k e(namespace_checked_publication_env le sequence returned)after))suffix
      (live(Callstate called arguments continuation final)) /\
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 29)k e le memory))
      (prefix++callback++guard)
      (live(State f_namespace_init(namespace_tail 30)k e(namespace_checked_publication_env le sequence returned)after)).
Proof.
  intros OTHER WRITE PRIVATE BAD REPORT SEQUENCE SEND ADMISSION CHECK RUN.
  destruct(namespace_normal_publication_first_callback e le memory k admission report sequence
    BAD REPORT SEQUENCE SEND ADMISSION CHECK)as[count PATH].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  destruct(callback_returns_before_private_write namespace_ge cell(Internal f_send_frame)
    [Vint report;Vlong sequence;Vptr admission Ptrofs.zero](namespace_publication_cont e le sequence k)memory grant_peer rest
    called arguments continuation final writeEvent writeAfter
    I (sender_excludes_private _ _ _ _ _ _ OTHER) TAIL WRITE PRIVATE)
    as[callback[remaining[value[after[ORDER[CALLEE CONTINUE]]]]]].
  destruct(namespace_publication_actual_return_type _ _ _ _ _ _ _ _ _ _ _ _ CONTINUE)as[returned SAME];subst value.
  destruct(namespace_publication_return_frontier e le after k sequence returned)as[guard_count GUARD].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ GUARD CONTINUE)
    as[endpoint[suffix[GUARD_EVENTS[SAME[GUARD_PREFIX FINAL]]]]];subst endpoint.
  exists(repeat namespace_source_event count),callback,(repeat namespace_source_event guard_count),suffix,returned,after.
  split;[rewrite EVENTS,ORDER,GUARD_EVENTS;repeat rewrite <-app_assoc;reflexivity|].
  split;[apply namespace_source_repeat|]. split;[apply namespace_source_repeat|].
  split;[exact CALLEE|]. split;[exact FINAL|].
  eapply namespace_steps_append;[exact PREFIX|].
  eapply namespace_steps_append;[exact(namespace_grant_plug_steps _ _ _ _ _ (namespace_publication_cont e le sequence k) I CALLEE)|exact GUARD_PREFIX].
Qed.
