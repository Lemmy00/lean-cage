(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: The actual helper's ordered calls act on its fork-owned task and cgroup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessStatus ProcessAllocation ProcessPlacement
  ProcessOwnership ProcessPhysicalTrace ProcessFileTrace ProcessAdmission ProcessAdmissionEvents.
From EntryNamespace Require Import NamespaceObjects.
Import ListNotations.
Open Scope Z_scope.

Lemma file_event_retains_lease event :process_file_frame_event event=true ->process_nonreaping event=true.
Proof.
  intros FILE;destruct event as[native|a b c d e|a b c d e|a b c d|a b c d| |a b c d|a b c|auxiliary];try exact FILE.
  destruct native as[library|a b c d|a b c|a b c|a b|a b c d|a b c|a b c|];try exact FILE.
  destruct library;try exact FILE;discriminate.
Qed.

Theorem actual_cgroup_writes_return_whole operation (linux:LinuxProcessContract operation)
    parent child before events after cgroup group :
  process_cgroup_files before parent cgroup=Some group ->
  Forall(fun event=>process_file_frame_event event=true)events ->
  process_world_steps operation parent child before events after ->
  process_cgroup_whole_returns cgroup events.
Proof.
  intros FILE EVENTS RUN;revert FILE EVENTS;induction RUN;intros FILE EVENTS;
    unfold process_cgroup_whole_returns;intros q bytes error MEMBER DESCRIPTOR WRITING;[contradiction|].
  inversion EVENTS as[|current tail HEAD TAIL_FILES];subst current tail.
  assert(OBSERVED:process_cgroup_files observed parent cgroup=Some group).
  { rewrite(interference_files _ _ _ _ H);exact FILE. }
  destruct MEMBER as[SAME|MEMBER].
  - subst event;eapply(linux_cgroup_count _ linux);[exact WRITING| |exact H0].
    rewrite DESCRIPTOR;exact OBSERVED.
  - assert(MIDDLE:process_cgroup_files middle parent cgroup=Some group).
    { rewrite(linux_fixed_file_frame _ linux _ _ parent _ HEAD H0);exact OBSERVED. }
    exact(IHRUN MIDDLE TAIL_FILES q bytes error MEMBER DESCRIPTOR WRITING).
Qed.

Lemma admission_source_quiet event :admission_quiet_event event ->process_quiet_event event=true.
Proof. intros[SAME|SAME];subst event;reflexivity. Qed.

Inductive admission_kernel_snapshots operation cell parent child before events after cgroup group : Prop :=
| admission_kernel_snapshots_intro : forall locals count bytes error word prefix between suffix
    write_boundary write_observed placed options_boundary options_observed configured,
    canonical_pid bytes child ->
    admission_is_stopped word=true ->admission_is_sigstop word=true ->
    (exists status offset,In(process_waited(task_pid child)status offset Int.zero
      (wait_status(task_pid child)word))prefix) ->
    events=prefix++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer bytes error))::
      (between++process_traced(Int.repr 16896)(task_pid child)(Vlong Int64.zero)
        (Vlong(Int64.repr 1048592))Int64.zero::suffix) ->
    process_world_steps operation parent child before prefix write_boundary ->
    ProcessInterference parent child write_boundary write_observed ->
    OwnsUnreaped write_observed parent child ->
    process_cgroup_files write_observed parent cgroup=Some group ->
    operation parent write_observed
      (placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer bytes error)))placed ->
    OwnsUnreaped placed parent child ->owned_cgroup(process_tasks placed child)=Some group ->
    process_world_steps operation parent child placed between options_boundary ->
    ProcessInterference parent child options_boundary options_observed ->
    operation parent options_observed(process_traced(Int.repr 16896)(task_pid child)(Vlong Int64.zero)
      (Vlong(Int64.repr 1048592))Int64.zero)configured ->
    OwnsStopped configured parent child ->owned_options(process_tasks configured child)=Int64.repr 1048592 ->
    owned_cgroup(process_tasks configured child)=Some group ->
    Forall admission_quiet_event suffix ->
    process_world_steps operation parent child configured suffix after ->
    admission_kernel_snapshots operation cell parent child before events after cgroup group.

Theorem actual_admission_establishes_scope_from_live_tls operation (linux:LinuxProcessContract operation)
    cell before_memory parent child before_world events after_memory after_world cgroup group status offset :
  1<=Int.signed(task_pid child) ->status<>tls_block cell ->Mem.valid_block before_memory(tls_block cell) ->
  OwnsUnreaped before_world parent child ->process_cgroup_files before_world parent cgroup=Some group ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint(task_pid child);Vint cgroup;Vptr status offset]Kstop before_memory))events
    (live(Returnstate(Vint Int.zero)Kstop after_memory)) ->
  process_world_steps operation parent child before_world events after_world ->
  admission_kernel_snapshots operation cell parent child before_world events after_world cgroup group.
Proof.
  intros POSITIVE SEPARATE ERRNO OWNER FILE SOURCE KERNEL.
  pose proof(admission_actual_file_frames_from_live_tls _ _ _ _ _ _ _ _ POSITIVE SEPARATE ERRNO SOURCE)as FILES.
  assert(WHOLE:process_cgroup_whole_returns cgroup events)
    by(eapply actual_cgroup_writes_return_whole;[exact linux|exact FILE|exact FILES|exact KERNEL]).
  destruct(admission_actual_source_guarantee_with_tail _ _ _ _ _ _ _ _ POSITIVE SEPARATE ERRNO WHOLE SOURCE)
    as(locals&count&bytes&error&word&before_stop&before_write&before_options&suffix&
      DIGITS&LEADING&NUMBER&STOP&SIGNAL&ORDER&BEFORE_STOP&BEFORE_WRITE&QUIET&TAIL_QUIET).
  set(prefix:=before_stop++process_waited(task_pid child)status offset Int.zero
    (wait_status(task_pid child)word)::before_write).
  assert(EVENTS:events=prefix++placement_lift(io_step(admission_write_request cell locals cgroup count)
    (transfer bytes error))::(before_options++process_traced(Int.repr 16896)(task_pid child)
      (Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero::suffix)).
  { unfold prefix;rewrite ORDER;repeat rewrite <-app_assoc;cbn[app];repeat rewrite <-app_assoc;reflexivity. }
  assert(PREFIX_FILES:Forall(fun event=>process_file_frame_event event=true)prefix).
  { rewrite EVENTS in FILES;apply Forall_app in FILES;exact(proj1 FILES). }
  assert(PREFIX_LEASE:Forall(fun event=>process_nonreaping event=true)prefix).
  { apply Forall_forall;intros event MEMBER.
    apply Forall_forall with(x:=event)in PREFIX_FILES;[apply file_event_retains_lease;exact PREFIX_FILES|exact MEMBER]. }
  rewrite EVENTS in KERNEL.
  destruct(process_world_split _ _ _ _ _ _ _ KERNEL)as[write_boundary[PREFIX REST]].
  assert(BOUNDARY_OWNER:OwnsUnreaped write_boundary parent child).
  { eapply process_trace_retains_incarnation;[exact linux|exact OWNER|exact PREFIX_LEASE|exact PREFIX]. }
  pose proof(process_trace_retains_file _ linux _ _ _ _ _ PREFIX_FILES PREFIX)as FILE_FRAME.
  inversion REST as[|start write_observed event placed remaining last INTERFERENCE CGSTEP AFTER_WRITE];
    subst start event remaining last.
  assert(WRITE_OWNER:OwnsUnreaped write_observed parent child)
    by(eapply unreaped_owner_survives_interference;[exact BOUNDARY_OWNER|exact INTERFERENCE]).
  assert(WRITE_FILE:process_cgroup_files write_observed parent cgroup=Some group).
  { rewrite(interference_files _ _ _ _ INTERFERENCE),FILE_FRAME;exact FILE. }
  assert(CANONICAL:canonical_pid bytes child)
    by(split;[exact DIGITS|];split;[exact LEADING|exact NUMBER]).
  assert(PLACED:OwnsUnreaped placed parent child /\owned_cgroup(process_tasks placed child)=Some group).
  { eapply(linux_cgroup_move _ linux)with(q:=admission_write_request cell locals cgroup count)
      (bytes:=bytes)(error:=error);
      [exact WRITE_OWNER|reflexivity|exact WRITE_FILE|exact CANONICAL|exact CGSTEP]. }
  destruct PLACED as[PLACED_OWNER PLACED_GROUP].
  destruct(process_world_split _ _ _ _ _ _ _ AFTER_WRITE)as[options_boundary[BETWEEN REST_OPTIONS]].
  assert(QUIET_FLAGS:Forall(fun event=>process_quiet_event event=true)before_options).
  { apply Forall_forall;intros event MEMBER;apply admission_source_quiet.
    apply Forall_forall with(x:=event)in QUIET;assumption. }
  destruct(process_trace_retains_scope _ linux _ _ _ _ _ PLACED_OWNER QUIET_FLAGS BETWEEN)
    as[OPTIONS_BOUNDARY_OWNER OPTIONS_BOUNDARY_GROUP].
  inversion REST_OPTIONS as[|start options_observed event configured remaining last OPTIONS_INTERFERENCE OPTIONS_STEP TAIL];
    subst start event remaining last.
  assert(OPTIONS_OWNER:OwnsUnreaped options_observed parent child)
    by(eapply unreaped_owner_survives_interference;[exact OPTIONS_BOUNDARY_OWNER|exact OPTIONS_INTERFERENCE]).
  assert(OPTIONS_GROUP:owned_cgroup(process_tasks options_observed child)=Some group).
  { rewrite(interference_owned_scope _ _ _ _ OPTIONS_BOUNDARY_OWNER OPTIONS_INTERFERENCE),
      OPTIONS_BOUNDARY_GROUP;exact PLACED_GROUP. }
  destruct(source_options_preserve_membership _ linux _ _ _ _ _ OPTIONS_OWNER OPTIONS_GROUP OPTIONS_STEP)
    as[STOPPED[OPTIONS CONFIGURED_GROUP]].
  eapply admission_kernel_snapshots_intro with(locals:=locals)(count:=count)(bytes:=bytes)(error:=error)
    (word:=word)(prefix:=prefix)(between:=before_options)(suffix:=suffix)
    (write_boundary:=write_boundary)(write_observed:=write_observed)(placed:=placed)
    (options_boundary:=options_boundary)(options_observed:=options_observed)(configured:=configured);
    try eassumption.
  exists status,offset;unfold prefix;apply in_or_app;right;left;reflexivity.
Qed.

Theorem actual_admission_establishes_scope operation (linux:LinuxProcessContract operation)
    cell before_memory parent child before_world events after_memory after_world cgroup group status offset :
  1<=Int.signed(task_pid child) ->status<>tls_block cell ->entry_errno_ready cell before_memory ->
  OwnsUnreaped before_world parent child ->process_cgroup_files before_world parent cgroup=Some group ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint(task_pid child);Vint cgroup;Vptr status offset]Kstop before_memory))events
    (live(Returnstate(Vint Int.zero)Kstop after_memory)) ->
  process_world_steps operation parent child before_world events after_world ->
  admission_kernel_snapshots operation cell parent child before_world events after_world cgroup group.
Proof.
  intros POSITIVE SEPARATE READY OWNER FILE SOURCE KERNEL.
  eapply actual_admission_establishes_scope_from_live_tls;try eassumption.
  destruct READY as[error[LOW[HIGH[ACCESS LOAD]]]].
  eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.

Theorem admission_snapshots_return_scope operation(linux:LinuxProcessContract operation)
    cell parent child before events after cgroup group:
  admission_kernel_snapshots operation cell parent child before events after cgroup group ->
  OwnsUnreaped after parent child /\owned_cgroup(process_tasks after child)=Some group.
Proof.
  intros SNAPSHOTS;destruct SNAPSHOTS as[locals count bytes error word prefix between suffix
    write_boundary write_observed placed options_boundary options_observed configured
    CANONICAL STOP SIGNAL STOP_EVENT EVENTS PREFIX INTERFERENCE WRITE_OWNER FILE CGSTEP
    PLACED_OWNER PLACED_GROUP BETWEEN OPTIONS_INTERFERENCE OPTIONS_STEP STOPPED OPTIONS GROUP QUIET TAIL].
  assert(FLAGS:Forall(fun event=>process_quiet_event event=true)suffix).
  { apply Forall_forall;intros event MEMBER;apply admission_source_quiet.
    apply Forall_forall with(x:=event)in QUIET;assumption. }
  destruct(process_trace_retains_scope _ linux _ _ _ _ _(proj1 STOPPED)FLAGS TAIL)
    as[OWNER FRAME];split;[exact OWNER|congruence].
Qed.

Theorem actual_admission_return_scope_from_live_tls operation(linux:LinuxProcessContract operation)
    cell before_memory parent child before_world events after_memory after_world cgroup group status offset:
  1<=Int.signed(task_pid child) ->status<>tls_block cell ->Mem.valid_block before_memory(tls_block cell) ->
  OwnsUnreaped before_world parent child ->process_cgroup_files before_world parent cgroup=Some group ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint(task_pid child);Vint cgroup;Vptr status offset]Kstop before_memory))events
    (live(Returnstate(Vint Int.zero)Kstop after_memory)) ->
  process_world_steps operation parent child before_world events after_world ->
  OwnsUnreaped after_world parent child /\owned_cgroup(process_tasks after_world child)=Some group.
Proof.
  intros POSITIVE SEPARATE ERRNO OWNER FILE SOURCE KERNEL.
  eapply admission_snapshots_return_scope;[exact linux|].
  eapply actual_admission_establishes_scope_from_live_tls;eassumption.
Qed.

Theorem actual_admission_return_scope operation(linux:LinuxProcessContract operation)
    cell before_memory parent child before_world events after_memory after_world cgroup group status offset:
  1<=Int.signed(task_pid child) ->status<>tls_block cell ->entry_errno_ready cell before_memory ->
  OwnsUnreaped before_world parent child ->process_cgroup_files before_world parent cgroup=Some group ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint(task_pid child);Vint cgroup;Vptr status offset]Kstop before_memory))events
    (live(Returnstate(Vint Int.zero)Kstop after_memory)) ->
  process_world_steps operation parent child before_world events after_world ->
  OwnsUnreaped after_world parent child /\owned_cgroup(process_tasks after_world child)=Some group.
Proof.
  intros POSITIVE SEPARATE READY OWNER FILE SOURCE KERNEL.
  eapply actual_admission_return_scope_from_live_tls;try eassumption.
  destruct READY as[error[LOW[HIGH[ACCESS LOAD]]]].
  eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.
