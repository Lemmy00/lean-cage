(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Source cursors select actual primitives and physical snapshots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessCallerConnection ProcessSourceOrigin
  ProcessOwnership ProcessPhysicalTrace ProcessScope.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace
  NamespacePhysical NamespaceSocket.
Import ListNotations.
Local Close Scope lean_scope.

Definition source_context_group(context:LeanCage_Entry_CallerPhysical_Context):option nat:=
  match LeanCage_Entry_CallerPhysical_Context_cgroup context with
  |ProcessImport.Option_none_inst1 _=>None
  |ProcessImport.Option_some_inst1 _ group=>Some(nat_of_Nat group)end.
Definition source_context_tracer(context:LeanCage_Entry_CallerPhysical_Context):option TaskIdentity:=
  match LeanCage_Entry_CallerPhysical_Context_tracer context with
  |ProcessImport.Option_none_inst1 _=>None
  |ProcessImport.Option_some_inst1 _ actor=>Some(physical_identity_task actor)end.

(* These are projections of one kernel task, rather than a new entry-state
   guarantee. The source and the Linux operation laws establish its fields. *)
Record SourceProcessView(world:ProcessWorld)(child:TaskIdentity)
    (context:LeanCage_Entry_CallerPhysical_Context):Prop:={
  source_view_group:owned_cgroup(process_tasks world child)=source_context_group context;
  source_view_tracer:owned_tracer(process_tasks world child)=source_context_tracer context;
  source_view_options:nat_of_Nat(LeanCage_Entry_CallerPhysical_Context_options context)=
    Z.to_nat(Int64.unsigned(owned_options(process_tasks world child)))
}.

Record SourceSnapshot:={
  source_process_before:ProcessWorld;
  source_process_after:ProcessWorld;
  source_namespace_before:NamespaceWorld;
  source_namespace_after:NamespaceWorld
}.

Definition SourceFileView(groups:nat->option nat)(process:ProcessWorld)(actor:TaskIdentity)
    (namespace:NamespaceWorld):Prop:=forall fd group,
  process_cgroup_files process actor fd=Some group <->
  exists binding object,namespace_table namespace fd=Some binding /\
    descriptor_object binding=ordinary_object object /\groups object=Some group.

Lemma source_physical_identity_injective left right:
  physical_identity_task left=physical_identity_task right ->left=right.
Proof.
  intro SAME.
  pose proof(f_equal(fun task=>Int.signed(task_pid task))SAME)as PID.
  cbv beta in PID.
  rewrite !physical_identity_task_pid in PID;apply Nat2Z.inj in PID.
  pose proof(f_equal task_incarnation SAME)as GENERATION.
  unfold physical_identity_task,physical_identity_incarnation in GENERATION;cbn in GENERATION.
  unfold physical_identity_pid in PID.
  apply(f_equal Nat_of_nat)in PID,GENERATION;rewrite !Nat2natid in PID,GENERATION.
  destruct left,right;cbn in PID,GENERATION;subst;reflexivity.
Qed.

Lemma source_physical_pid_word child:
  caller_request_nat(task_pid(physical_identity_task child))=LeanCage_Entry_ProcessIdentity_pid child.
Proof.
  pose proof(physical_identity_pid_range child)as RANGE.
  change(1<=Z.of_nat(physical_identity_pid child)<=2147483647)%Z in RANGE.
  unfold caller_request_nat,physical_identity_task;cbn[task_pid].
  rewrite Int.unsigned_repr by(change(0<=Z.of_nat(physical_identity_pid child)<=4294967295)%Z;lia).
  rewrite Nat2Z.id;unfold physical_identity_pid;apply Nat2natid.
Qed.

Lemma source_view_has_group world child context group:
  SourceProcessView world child context ->owned_cgroup(process_tasks world child)=Some group ->
  LeanCage_Entry_CallerPhysical_Context_cgroup context=
    ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group).
Proof.
  intros VIEW GROUP;pose proof(source_view_group _ _ _ VIEW)as OBSERVED.
  rewrite GROUP in OBSERVED;unfold source_context_group in OBSERVED.
  destruct(LeanCage_Entry_CallerPhysical_Context_cgroup context);[discriminate|].
  inversion OBSERVED;rewrite Nat2natid;reflexivity.
Qed.

Lemma source_view_has_options world child context options:
  SourceProcessView world child context ->owned_options(process_tasks world child)=options ->
  LeanCage_Entry_CallerPhysical_Context_options context=caller_options_nat options.
Proof.
  intros VIEW OPTIONS;pose proof(source_view_options _ _ _ VIEW)as OBSERVED.
  rewrite OPTIONS in OBSERVED;apply(f_equal Nat_of_nat)in OBSERVED;rewrite Nat2natid in OBSERVED.
  exact OBSERVED.
Qed.

Lemma source_view_has_tracer world child context actor:
  SourceProcessView world child context ->owned_tracer(process_tasks world child)=Some(physical_identity_task actor) ->
  LeanCage_Entry_CallerPhysical_Context_tracer context=
    ProcessImport.Option_some_inst1 LeanCage_Entry_ProcessIdentity actor.
Proof.
  intros VIEW TRACER;pose proof(source_view_tracer _ _ _ VIEW)as OBSERVED.
  rewrite TRACER in OBSERVED;unfold source_context_tracer in OBSERVED.
  destruct(LeanCage_Entry_CallerPhysical_Context_tracer context)as[|actual];[discriminate|].
  assert(SAME:physical_identity_task actor=physical_identity_task actual)by congruence.
  apply source_physical_identity_injective in SAME;subst actual;reflexivity.
Qed.

(* Each clause describes one actual C primitive at its linearization point.
   In particular, it does not authorize a write, supply its arguments, order
   another operation, or assert an entry/scope property of a whole execution. *)
Record SourcePrimitive
    (operation:TaskIdentity->ProcessWorld->process_event->ProcessWorld->Prop)
    (groups:nat->option nat)
    (child:LeanCage_Entry_ProcessIdentity)(actor:LeanCage_Entry_ProcessIdentity)
    (event:namespace_event)(tick:LeanCage_Entry_CallerPhysical_Tick)(snapshot:SourceSnapshot):Prop:={
  source_primitive_task:namespace_task(source_namespace_before snapshot)=physical_identity_task actor;
  source_primitive_caller_live:
    owned_phase(process_tasks(source_process_before snapshot)(physical_identity_task actor))<>task_exited;
  source_primitive_before:SourceProcessView(source_process_before snapshot)(physical_identity_task child)
    (LeanCage_Entry_CallerPhysical_Tick_before tick);
  source_primitive_after:SourceProcessView(source_process_after snapshot)(physical_identity_task child)
    (LeanCage_Entry_CallerPhysical_Tick_after tick);
  source_primitive_namespace:namespace_kernel_event(source_namespace_before snapshot)event
    (source_namespace_after snapshot);
  source_primitive_process:forall original,event=namespace_process original ->
    operation(physical_identity_task actor)(source_process_before snapshot)original(source_process_after snapshot);
  source_primitive_table:forall fd,
    physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd=
      namespace_table(source_namespace_before snapshot)fd;
  source_primitive_files_before:SourceFileView groups(source_process_before snapshot)
    (physical_identity_task actor)(source_namespace_before snapshot);
  source_primitive_files_after:SourceFileView groups(source_process_after snapshot)
    (physical_identity_task actor)(source_namespace_after snapshot);
  source_primitive_ptrace:forall request target address data returned,
    event=namespace_process(process_traced request target address data returned) ->
    caller_request_nat target=LeanCage_Entry_ProcessIdentity_pid child ->
    LeanCage_Entry_CallerPhysical_Tick_action tick=
      LeanCage_Entry_CallerPhysical_Action_request actor(caller_request_nat request)
        (caller_options_nat(caller_payload_word data));
  source_primitive_ptrace_lost:forall request target address data,
    event=namespace_process(process_trace_lost request target address data) ->
    caller_request_nat target=LeanCage_Entry_ProcessIdentity_pid child ->
    LeanCage_Entry_CallerPhysical_Tick_action tick=
      LeanCage_Entry_CallerPhysical_Action_request actor(caller_request_nat request)
        (caller_options_nat(caller_payload_word data));
  source_primitive_write:forall io,namespace_socket_io event=Some io ->
    IO.operation(source_socket_request io)=writing ->
    ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor
      (caller_request_nat(descriptor(source_socket_request io)))
      (journal_byte_values(source_socket_bytes io))(journal_lost_value(source_socket_lost io));
  source_primitive_cgroup:forall q bytes error group,
    event=namespace_process(process_machine_event(io_step q(transfer bytes error))) ->
    IO.operation q=writing ->
    process_cgroup_files(source_process_before snapshot)(physical_identity_task actor)(descriptor q)=Some group ->
    canonical_pid bytes(physical_identity_task child) ->
    LeanCage_Entry_CallerPhysical_Tick_action tick=
      LeanCage_Entry_CallerPhysical_Action_placement(Nat_of_nat group);
  source_primitive_close:forall fd reply,
    event=namespace_process(process_entry(entry_library(close_returned fd reply))) ->
    LeanCage_Entry_CallerPhysical_Tick_action tick=LeanCage_Entry_CallerPhysical_Action_idle;
  source_primitive_label:LeanCage_Entry_CallerPhysical_Tick_primitive tick=
    ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_PrimitiveLabel
}.

(* The interpreter advances a C program only by its next actual source event.
   External/native ticks retain their positions. The primitive relation above
   is the single-operation runtime mapping, not a source-authorization premise. *)
Inductive SourceEventSchedule
    (primitive:LeanCage_Entry_ProcessIdentity->namespace_event->
      LeanCage_Entry_CallerPhysical_Tick->SourceSnapshot->Prop)
    (runs:list CallerSourceRun):
    (nat->nat)->list LeanCage_Entry_CallerPhysical_Tick->(nat->nat)->Prop:=
| source_event_done:forall before,SourceEventSchedule primitive runs before[]before
| source_event_external:forall before tick ticks after,
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference ->
    SourceEventSchedule primitive runs before ticks after ->
    SourceEventSchedule primitive runs before(tick::ticks)after
| source_event_next:forall before tick ticks after run program event snapshot,
    nth_error runs program=Some run ->
    nth_error(source_events run)(before program)=Some event ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program(before program) ->
    primitive(source_actor run)event tick snapshot ->
    SourceEventSchedule primitive runs(source_cursor_next before program)ticks after ->
    SourceEventSchedule primitive runs before(tick::ticks)after.

Theorem source_event_schedule_erases primitive runs before ticks after:
  SourceEventSchedule primitive runs before ticks after ->SourceSchedule before ticks after.
Proof.
  intro RUN;induction RUN.
  - constructor.
  - eapply source_schedule_next;[eapply source_cursor_external;exact H|exact IHRUN].
  - eapply source_schedule_next;[eapply source_cursor_advance;exact H1|exact IHRUN].
Qed.

Theorem source_event_schedule_selected primitive runs before ticks after offset tick program ordinal:
  SourceEventSchedule primitive runs before ticks after ->nth_error ticks offset=Some tick ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  exists run event snapshot,nth_error runs program=Some run /\
    nth_error(source_events run)ordinal=Some event /\primitive(source_actor run)event tick snapshot.
Proof.
  intro RUN;revert offset;induction RUN;intros[|offset]SELECTED SOURCE;try discriminate.
  - inversion SELECTED;subst;rewrite SOURCE in H;discriminate.
  - eapply IHRUN;eassumption.
  - inversion SELECTED;subst.
    assert(REFERENCE:source_reference program0(before program0)=source_reference program ordinal)by congruence.
    destruct(source_reference_injective _ _ _ _ REFERENCE)as[PROGRAM ORDINAL];subst program0 ordinal.
    exists run,event,snapshot;repeat split;assumption.
  - eapply IHRUN;eassumption.
Qed.

Theorem source_event_schedule_covers primitive runs before ticks after program ordinal run event:
  SourceEventSchedule primitive runs before ticks after ->
  (before program<=ordinal<after program)%nat ->
  nth_error runs program=Some run ->nth_error(source_events run)ordinal=Some event ->
  exists offset tick snapshot,nth_error ticks offset=Some tick /\
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal /\
    primitive(source_actor run)event tick snapshot.
Proof.
  intros RUN BOUNDS PROGRAM EVENT.
  destruct(source_schedule_covers _ _ _ _ _(source_event_schedule_erases _ _ _ _ _ RUN)BOUNDS)
    as[offset[tick[SELECTED SOURCE]]].
  destruct(source_event_schedule_selected _ _ _ _ _ _ _ _ _ RUN SELECTED SOURCE)
    as[actual[observed[snapshot[ACTUAL[OBSERVED PRIMITIVE]]]]].
  assert(ACTUAL_RUN:actual=run)by congruence;subst actual.
  assert(ACTUAL_EVENT:observed=event)by congruence;subst observed.
  exists offset,tick,snapshot;repeat split;assumption.
Qed.

Theorem recorded_source_cgroup_membership operation(linux:LinuxProcessContract operation) groups
    child actor event tick snapshot q bytes error group:
  SourcePrimitive operation groups child actor event tick snapshot ->
  event=namespace_process(process_machine_event(io_step q(transfer bytes error))) ->
  OwnsUnreaped(source_process_before snapshot)(physical_identity_task actor)(physical_identity_task child) ->
  IO.operation q=writing ->
  process_cgroup_files(source_process_before snapshot)(physical_identity_task actor)(descriptor q)=Some group ->
  canonical_pid bytes(physical_identity_task child) ->
  LeanCage_Entry_CallerPhysical_Tick_action tick=
    LeanCage_Entry_CallerPhysical_Action_placement(Nat_of_nat group) /\
  LeanCage_Entry_CallerPhysical_Context_cgroup(LeanCage_Entry_CallerPhysical_Tick_after tick)=
    ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group).
Proof.
  intros PRIMITIVE EVENT OWNER WRITING FILE BYTES;split.
  - eapply source_primitive_cgroup;eassumption.
  - pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE _ EVENT)as STEP.
    destruct(linux_cgroup_move _ linux _ _ _ _ _ _ _ _ OWNER WRITING FILE BYTES STEP)as[OWNED GROUP].
    eapply source_view_has_group;[eapply source_primitive_after;exact PRIMITIVE|exact GROUP].
Qed.

Theorem recorded_source_options operation(linux:LinuxProcessContract operation) groups
    child actor event tick snapshot options:
  SourcePrimitive operation groups child actor event tick snapshot ->
  event=namespace_process(process_traced(Int.repr 16896)(task_pid(physical_identity_task child))
    (Vlong Int64.zero)(Vlong options)Int64.zero) ->
  OwnsUnreaped(source_process_before snapshot)(physical_identity_task actor)(physical_identity_task child) ->
  LeanCage_Entry_CallerPhysical_Tick_action tick=
    LeanCage_Entry_CallerPhysical_Action_request actor(caller_request_nat(Int.repr 16896))(caller_options_nat options) /\
  LeanCage_Entry_CallerPhysical_Context_options(LeanCage_Entry_CallerPhysical_Tick_after tick)=caller_options_nat options /\
  LeanCage_Entry_CallerPhysical_Context_tracer(LeanCage_Entry_CallerPhysical_Tick_after tick)=
    ProcessImport.Option_some_inst1 LeanCage_Entry_ProcessIdentity actor /\
  OwnsStopped(source_process_after snapshot)(physical_identity_task actor)(physical_identity_task child).
Proof.
  intros PRIMITIVE EVENT OWNER.
  pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE _ EVENT)as STEP.
  destruct(linux_ptrace_options _ linux _ _ _ _ _ OWNER STEP)as[INITIAL[STOPPED[OPTIONS FRAME]]].
  split.
  - exact(source_primitive_ptrace _ _ _ _ _ _ _ PRIMITIVE
      (Int.repr 16896)(task_pid(physical_identity_task child))(Vlong Int64.zero)(Vlong options)
      Int64.zero EVENT(source_physical_pid_word child)).
  - split;[eapply source_view_has_options;[eapply source_primitive_after;exact PRIMITIVE|exact OPTIONS]|].
    split;[|exact STOPPED].
    eapply source_view_has_tracer;[eapply source_primitive_after;exact PRIMITIVE|exact(proj2(proj2 STOPPED))].
Qed.

Theorem recorded_source_options_before operation(linux:LinuxProcessContract operation) groups
    child actor event tick snapshot options:
  SourcePrimitive operation groups child actor event tick snapshot ->
  event=namespace_process(process_traced(Int.repr 16896)(task_pid(physical_identity_task child))
    (Vlong Int64.zero)(Vlong options)Int64.zero) ->
  OwnsUnreaped(source_process_before snapshot)(physical_identity_task actor)(physical_identity_task child) ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_tracer(LeanCage_Entry_CallerPhysical_Tick_before tick))
    (ProcessImport.Option_some_inst1 LeanCage_Entry_ProcessIdentity actor).
Proof.
  intros PRIMITIVE EVENT OWNER.
  pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE _ EVENT)as STEP.
  destruct(linux_ptrace_options _ linux _ _ _ _ _ OWNER STEP)as[INITIAL REST].
  pose proof(source_view_has_tracer _ _ _ actor(source_primitive_before _ _ _ _ _ _ _ PRIMITIVE)
    (proj2(proj2 INITIAL)))as TRACER.
  rewrite TRACER;constructor.
Qed.

Theorem recorded_source_resume operation(linux:LinuxProcessContract operation) groups
    child actor event tick snapshot group options:
  SourcePrimitive operation groups child actor event tick snapshot ->
  event=namespace_process(process_traced(Int.repr 7)(task_pid(physical_identity_task child))
    (Vlong Int64.zero)(Vlong Int64.zero)Int64.zero) ->
  OwnsUnreaped(source_process_before snapshot)(physical_identity_task actor)(physical_identity_task child) ->
  owned_cgroup(process_tasks(source_process_before snapshot)(physical_identity_task child))=Some group ->
  owned_options(process_tasks(source_process_before snapshot)(physical_identity_task child))=options ->
  LeanCage_Entry_CallerPhysical_Tick_action tick=
    LeanCage_Entry_CallerPhysical_Action_request actor(caller_request_nat(Int.repr 7))(caller_options_nat Int64.zero) /\
  LeanCage_Entry_CallerPhysical_Context_cgroup(LeanCage_Entry_CallerPhysical_Tick_after tick)=
    ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group) /\
  LeanCage_Entry_CallerPhysical_Context_options(LeanCage_Entry_CallerPhysical_Tick_after tick)=caller_options_nat options /\
  LeanCage_Entry_CallerPhysical_Context_tracer(LeanCage_Entry_CallerPhysical_Tick_after tick)=
    ProcessImport.Option_some_inst1 LeanCage_Entry_ProcessIdentity actor /\
  owned_phase(process_tasks(source_process_after snapshot)(physical_identity_task child))=task_running.
Proof.
  intros PRIMITIVE EVENT OWNER GROUP OPTIONS.
  pose proof(source_primitive_process _ _ _ _ _ _ _ PRIMITIVE _ EVENT)as STEP.
  destruct(linux_ptrace_continue _ linux _ _ _ _ OWNER STEP)
    as[STOPPED[OWNED[RUNNING[TRACER[OFRAME GFRAME]]]]].
  split.
  - exact(source_primitive_ptrace _ _ _ _ _ _ _ PRIMITIVE
      (Int.repr 7)(task_pid(physical_identity_task child))(Vlong Int64.zero)(Vlong Int64.zero)
      Int64.zero EVENT(source_physical_pid_word child)).
  - split;[eapply source_view_has_group;[eapply source_primitive_after;exact PRIMITIVE|congruence]|].
    split;[eapply source_view_has_options;[eapply source_primitive_after;exact PRIMITIVE|congruence]|].
    split;[eapply source_view_has_tracer;[eapply source_primitive_after;exact PRIMITIVE|exact TRACER]|exact RUNNING].
Qed.

Theorem recorded_source_close operation groups child actor event tick snapshot fd reply:
  SourcePrimitive operation groups child actor event tick snapshot ->
  event=namespace_process(process_entry(entry_library(close_returned fd reply))) ->
  LeanCage_Entry_CallerPhysical_Tick_action tick=LeanCage_Entry_CallerPhysical_Action_idle /\
  close_table(namespace_table(source_namespace_before snapshot))fd reply
    (namespace_table(source_namespace_after snapshot)).
Proof.
  intros PRIMITIVE EVENT;split;[eapply source_primitive_close;eassumption|].
  pose proof(source_primitive_namespace _ _ _ _ _ _ _ PRIMITIVE)as STEP;rewrite EVENT in STEP.
  destruct(namespace_close_kernel_details _ _ _ _ STEP)as[table[CLOSE AFTER]].
  rewrite AFTER;exact CLOSE.
Qed.
