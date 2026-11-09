(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The exact physical send consumes one recorded fork's checked source authorization. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Clight.
From LeanImport Require Import Lean.
Require Import IO Machine ArgumentsImport.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput NativeHandoffWire NativeValues.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessSourceRecording ProcessSourceTables
  ProcessCallerConnection ProcessSourceOrigin ProcessReleaseSafety.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceMachine NamespaceMemory NamespacePaths NamespaceCaller
  NamespaceStructure NamespaceTraceRegion NamespaceChildResult NamespaceForkPrefix NamespaceFork NamespaceForkInputs NamespaceSourceFork
  NamespaceGrantInputs NamespaceForkOwnership NamespaceForkGrant NamespaceSocket NamespacePhysical NamespaceChannel NamespaceGrant
  NamespaceSourceOwnership NamespaceWriteOrigin NamespacePostForkClosure NamespaceParentEntry NamespaceParentSafety.
Import ListNotations.
Local Close Scope lean_scope.

Lemma physical_grant_fork_body run returned(fork:ActualSourceFork run returned):
  skipn(S(length(source_fork_common _ _ fork)))(source_events run)=source_fork_body _ _ fork.
Proof.
  rewrite(source_fork_events _ _ fork),skipn_app.
  rewrite skipn_all2 by lia;replace(S(length(source_fork_common _ _ fork))-length(source_fork_common _ _ fork))%nat with 1%nat by lia.
  cbn;reflexivity.
Qed.

Theorem actual_same_fork_physical_send_authorized operation groups runs cursor worlds ticks final final_worlds
    scope first second failure reply world before_world snapshot owner child parent_program run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))child_memory
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))cgroup_binding report_binding channel
    send_offset sent_tick source_fd bytes lost binding:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  SourceProgramOwner runs owner parent_program ->nth_error runs parent_program=Some run ->
  cursor parent_program=S(length(source_fork_common _ _ fork)) ->worlds parent_program=world ->
  scope_history scope=[] ->source_cell run=scope_cell scope ->
  ChildPrefixResult scope(namespace_fd_events(source_fork_common _ _ fork))
    (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)) ->
  namespace_fd_events(source_fork_common _ _ fork)=child_signal_log scope first second failure reply ->
  NamespaceWorldTrace.namespace_kernel_steps before_world(source_fork_common _ _ fork)world ->
  fork_matches world snapshot ->fork_child snapshot=physical_identity_task child ->
  NativeForkCopy(scope_cell scope)(source_fork_before _ _ fork)(source_fork_parent _ _ fork)child_memory ->
  Lean.eq(argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight(scope_borrowed scope))))
    (argument_bytes(map Byte.repr[114;117;110])) ->
  namespace_table before_world(prepared_cgroup_fd input)=Some cgroup_binding ->
  namespace_table before_world(prepared_report_fd input)=Some report_binding ->
  namespace_table world first=Some(endpoint_binding channel parent_endpoint) ->
  nth_error ticks send_offset=Some sent_tick ->SourceIO runs sent_tick ->
  (exists reference,LeanCage_Entry_CallerPhysical_Tick_source sent_tick=
    ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference reference) ->
  physical_tick_projection channel sent_tick=(physical_tick_table sent_tick,
    channel_sent(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))source_fd bytes lost) ->
  physical_tick_table sent_tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))source_fd=Some binding ->
  descriptor_object binding=release_endpoint channel parent_endpoint ->
  exists source_ordinal event io finish_prefix setup_prefix ready grant_prefix release_prefix source_resume
      resume_offset resume_tick resume_snapshot,
    Forall(fun event=>namespace_parent_prelude_event event=true)(finish_prefix++setup_prefix) /\
    Forall(namespace_parent_closes_from[failure;scope_input scope;scope_output scope;scope_errors scope;prepared_parent_fd input])
      (finish_prefix++setup_prefix) /\
    source_fd=first /\nth_error(source_events run)source_ordinal=Some event /\namespace_socket_io event=Some io /\
    descriptor(source_socket_request io)=source_fd /\source_socket_bytes io=bytes /\source_socket_lost io=lost /\
    LeanCage_Entry_CallerPhysical_Tick_source sent_tick=source_reference parent_program source_ordinal /\
    firstn(source_ordinal-S(length(source_fork_common _ _ fork)))(source_fork_body _ _ fork)=
      finish_prefix++setup_prefix++grant_prefix++release_prefix /\
    namespace_steps ProcessGlobalCalls.caller_ge(source_cell run)
      (live(Returnstate(Vint(task_pid(fork_child snapshot)))(source_fork_continuation _ _ fork)(source_fork_parent _ _ fork)))
      (finish_prefix++setup_prefix)
      (live(State f_namespace_init(namespace_tail 20)Kstop(prepared_parent_env input)
        (namespace_parent_setup_env(prepared_parent_temps input)(task_pid(fork_child snapshot)))ready)) /\
    namespace_authorized_parent(scope_cell scope)ready(task_pid(fork_child snapshot))first(prepared_cgroup_fd input)
      (prepared_status_cell input)(prepared_result_temporary input)(prepared_admission_cell input)
      (prepared_report_fd input)(prepared_sequence input)grant_prefix /\
    nth_error(source_events run)source_resume=Some(namespace_process(release_resume_event(task_pid(fork_child snapshot)))) /\
    (S(length(source_fork_common _ _ fork))+length finish_prefix+length setup_prefix+length grant_prefix<=source_resume)%nat /\
    (S(length(source_fork_common _ _ fork))<=source_resume<source_ordinal)%nat /\
    requested(source_socket_request io)=1 /\source_socket_bytes io=[Byte.repr 165] /\
    nth_error ticks resume_offset=Some resume_tick /\(resume_offset<send_offset)%nat /\
    LeanCage_Entry_CallerPhysical_Tick_source resume_tick=source_reference parent_program source_resume /\
    SourcePrimitive operation groups child owner
      (namespace_process(release_resume_event(task_pid(fork_child snapshot))))resume_tick resume_snapshot /\
    LeanCage_Entry_CallerPhysical_Tick_action resume_tick=
      LeanCage_Entry_CallerPhysical_Action_request owner(Nat_of_nat 7)(Nat_of_nat 0).
Proof.
  intros TABLES OWNER PROGRAM CURSOR WORLD HISTORY CELL FRONTIER LOG KERNEL MATCH CHILD COPY MODE CGROUP REPORT PEER
    SELECTED IO REFERENCE PROJECT PRESENT OBJECT.
  assert(ACTOR:source_actor run=owner)by(eapply source_owner_actor;eassumption).
  assert(FRONTIER_LOG:ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[](source_fork_continuation _ _ fork)(source_fork_before _ _ fork)))
    by(rewrite <-LOG;exact FRONTIER).
  destruct(actual_common_fork_continuation _ _ _ _ _ _ _ FRONTIER_LOG)as[fork_temps FORK_CONT].
  destruct(actual_parent_send_resolves_program runs(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))parent_program run
    sent_tick channel source_fd bytes lost PROGRAM(actual_program_owner_produces_key_domain _ _ _ OWNER)IO PROJECT REFERENCE)
    as[ordinal[event[io[EVENT[SOCKET[WRITING[DESCRIPTOR[BYTES[LOST SOURCE]]]]]]]]].
  assert(PARENT_PROFILE:Forall(fun event=>NamespaceDescriptorFrame.namespace_after_fork_event event=true)
    (skipn(cursor parent_program)(source_events run))).
  { rewrite CURSOR,physical_grant_fork_body.
    pose proof(source_fork_suffix _ _ fork)as RUN.
    rewrite CELL,FORK_CONT,(prepared_parent_continuation input)in RUN.
    eapply actual_fork_return_no_capability_export;[exact(prepared_parent_global input)|exact RUN]. }
  assert(INITIAL:NamespaceEndpoint.unique_parent_endpoint(namespace_table(worlds parent_program))channel first).
  { rewrite WORLD;eapply actual_common_fork_unique_parent with(le:=fork_temps)(memory:=source_fork_before _ _ fork).
    - exact HISTORY.
    - rewrite <-FORK_CONT;exact FRONTIER.
    - exact LOG.
    - exact KERNEL.
    - exact PEER. }
  pose proof(source_table_selected_unique_parent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    TABLES SELECTED SOURCE PROGRAM PARENT_PROFILE INITIAL)as UNIQUE.
  rewrite ACTOR in UNIQUE.
  assert(FD:source_fd=first)by(eapply UNIQUE;eassumption).
  assert(LOWER:(S(length(source_fork_common _ _ fork))<=ordinal)%nat).
  { pose proof(source_table_schedule_erases _ _ _ _ _ _ _ TABLES)as EVENTS.
    pose proof(source_event_schedule_erases _ _ _ _ _ EVENTS)as SCHEDULE.
    destruct(source_schedule_selected _ _ _ _ _ _ _ SCHEDULE SELECTED SOURCE)as[LOW HIGH].
    rewrite CURSOR in LOW;exact LOW. }
  destruct(actual_same_fork_source_write_authorized scope first second failure reply world before_world snapshot run fork
    child_memory input cgroup_binding report_binding ordinal event io HISTORY CELL FRONTIER LOG KERNEL MATCH COPY MODE
    CGROUP REPORT LOWER EVENT SOCKET WRITING ltac:(rewrite DESCRIPTOR;exact FD))
    as[finish_prefix[setup_prefix[ready[grant_prefix[release_prefix[resume FACTS]]]]]].
  destruct FACTS as[QUIET[CLOSED[ORDER[SETUP[AUTHORIZED[RESUMED[AFTER[BEFORE[COUNT CONTENT]]]]]]]]].
  assert(BOUNDS:(cursor parent_program<=resume<ordinal)%nat)by(rewrite CURSOR;exact BEFORE).
  destruct(source_table_before_selected _ _ _ _ _ _ _ send_offset sent_tick parent_program ordinal resume run
    (namespace_process(release_resume_event(task_pid(fork_child snapshot))))
    TABLES SELECTED SOURCE BOUNDS PROGRAM RESUMED)
    as[resume_offset[resume_tick[snapshot'[OFFSET[OBSERVED[AT PRIMITIVE]]]]]].
  rewrite ACTOR in PRIMITIVE.
  assert(ACTION:LeanCage_Entry_CallerPhysical_Tick_action resume_tick=
    LeanCage_Entry_CallerPhysical_Action_request owner(Nat_of_nat 7)(Nat_of_nat 0)).
  { pose proof(source_primitive_ptrace _ _ _ _ _ _ _ PRIMITIVE(Int.repr 7)(task_pid(fork_child snapshot))
      (Vlong Int64.zero)(Vlong Int64.zero)Int64.zero(Logic.eq_refl _)
      ltac:(rewrite CHILD;apply source_physical_pid_word))as OBSERVED_ACTION.
    exact OBSERVED_ACTION. }
  exists ordinal,event,io,finish_prefix,setup_prefix,ready,grant_prefix,release_prefix,resume,
    resume_offset,resume_tick,snapshot';repeat first[assumption|split].
Qed.
