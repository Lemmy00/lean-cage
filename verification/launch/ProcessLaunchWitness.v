(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: A useful launch starts untraced and changes scope only at its actual write. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From compcert Require Import AST Integers Values Memory Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine LibraryPreservation ProcessEffects ErrorNumber StoreSteps.
From EntryNative Require Import NativeHandoffMachine.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceLibrary NamespacePaths NamespaceParentWitness
  NamespaceLaunchWitness NamespaceKernel NamespaceWorldTrace.
From EntryNamespace Require Import NamespaceForkWorldWitness.
From EntryNamespace Require Import NamespaceDescriptorFrame.
From EntryProcess Require Import ProcessMachine ProcessStatus ProcessOwnership ProcessPhysicalTrace
  ProcessPhysicalWitness ProcessAllocation ProcessPlacement ProcessStructure ProcessPaths ProcessCallee
  ProcessClock ProcessClockMemory ProcessClockRun ProcessReleaseWitness ProcessSourceRecording.
Import ListNotations.
Open Scope Z_scope.

(* This finite useful model inhabits the primitive laws. The entry theorems
   still quantify over the broad failure/interference relations. Both process
   identities are the identities of the actual useful common fork. *)
Definition launch_world files tracer phase options group:ProcessWorld:={|
  process_pid:=fun pid=>if Int.eq pid(Int.repr 2)then Some physical_child else None;
  process_tasks:=fun _=>{|owned_parent:=physical_parent;owned_phase:=phase;
    owned_tracer:=tracer;owned_options:=options;owned_cgroup:=group|};
  process_cgroup_files:=files;
  process_explicit_reap:=fun _=>true;process_sole_waiter:=fun _=>true|}.

Lemma launch_owns files tracer phase options group:
  OwnsUnreaped(launch_world files tracer phase options group)physical_parent physical_child.
Proof. unfold OwnsUnreaped,launch_world,physical_child;cbn;rewrite Int.eq_true;auto. Qed.

Lemma launch_owner_unique files tracer phase options group parent child:
  OwnsUnreaped(launch_world files tracer phase options group)parent child ->
  parent=physical_parent /\child=physical_child.
Proof.
  intros[PID[PARENT REST]];cbn in PID,PARENT.
  destruct(Int.eq(task_pid child)(Int.repr 2));[inversion PID;auto|discriminate].
Qed.

Lemma launch_transport_owner files tracer phase options group next_files next_tracer next_phase next_options next_group parent child:
  OwnsUnreaped(launch_world files tracer phase options group)parent child ->
  OwnsUnreaped(launch_world next_files next_tracer next_phase next_options next_group)parent child.
Proof. intro OWN;destruct(launch_owner_unique _ _ _ _ _ _ _ OWN)as[PARENT CHILD];subst;apply launch_owns. Qed.

Lemma launch_stopped files options group:
  OwnsStopped(launch_world files(Some physical_parent)task_traced_stop options group)physical_parent physical_child.
Proof. split;[apply launch_owns|];split;reflexivity. Qed.

Definition launch_task_eq(left right:TaskIdentity):bool:=
  Int.eq(task_pid left)(task_pid right)&&Nat.eqb(task_incarnation left)(task_incarnation right).
Lemma launch_task_eq_same actor:launch_task_eq actor actor=true.
Proof. unfold launch_task_eq;rewrite Int.eq_true,Nat.eqb_refl;reflexivity. Qed.

Lemma launch_task_eq_sound left right:launch_task_eq left right=true ->left=right.
Proof.
  unfold launch_task_eq;rewrite andb_true_iff;intros[PID INC].
  apply Int.same_if_eq in PID;apply Nat.eqb_eq in INC.
  destruct left,right;cbn in PID,INC;subst;reflexivity.
Qed.

Definition launch_close_files(files:TaskIdentity->int->option nat)actor fd:=fun task descriptor=>
  if launch_task_eq task actor&&Int.eq descriptor fd then None else files task descriptor.
Definition launch_exec_files(files:TaskIdentity->int->option nat)actor:=fun task descriptor=>
  if launch_task_eq task actor then None else files task descriptor.

Definition launch_passive event:=match event with
  |process_waited _ _ _ _ _|process_traced _ _ _ _ _|process_trace_lost _ _ _ _=>false
  |process_entry(entry_flags_returned _ _ _)=>false
  |process_entry(entry_library(close_returned _ _))=>false
  |_=>process_quiet_event event end.

Inductive launch_operation(actor:TaskIdentity):ProcessWorld->process_event->ProcessWorld->Prop:=
| launch_neutral:forall world event,
    launch_passive event=true ->
    launch_operation actor world event world
| launch_io:forall files tracer phase options group q reply,
    files actor(IO.descriptor q)=None ->
    launch_operation actor(launch_world files tracer phase options group)
      (process_machine_event(io_step q reply))(launch_world files tracer phase options group)
| launch_close:forall files tracer phase options group fd reply,
    launch_operation actor(launch_world files tracer phase options group)
      (process_entry(entry_library(close_returned fd reply)))
      (launch_world(launch_close_files files actor fd)tracer phase options group)
| launch_image:forall files tracer phase options group path arguments environment,
    launch_operation actor(launch_world files tracer phase options group)
      (process_entry(entry_image path arguments environment))
      (launch_world(launch_exec_files files actor)tracer phase options group)
| launch_flags:forall files tracer phase options group fd flags,
    (flags=Int.zero\/flags=Int.one) ->
    launch_operation actor(launch_world files tracer phase options group)
      (process_entry(entry_flags_returned fd flags Int.zero))(launch_world files tracer phase options group)
| launch_wait_stop:forall files options group status offset word,
    actor=physical_parent ->admission_is_stopped word=true ->admission_is_sigstop word=true ->
    launch_operation actor(launch_world files(Some physical_parent)task_traced_stop options group)
      (process_waited(Int.repr 2)status offset Int.zero(wait_status(Int.repr 2)word))
      (launch_world files(Some physical_parent)task_traced_stop options group)
| launch_place:forall files tracer phase options group q bytes error assigned,
    files actor(IO.descriptor q)=Some assigned ->IO.operation q=writing ->
    Z.of_nat(length bytes)=requested q ->canonical_pid bytes physical_child ->
    launch_operation actor(launch_world files tracer phase options group)
      (process_machine_event(io_step q(transfer bytes error)))
      (launch_world files tracer phase options(Some assigned))
| launch_options:forall files group,
    actor=physical_parent ->
    launch_operation actor(launch_world files(Some physical_parent)task_traced_stop Int64.zero group)
      (process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero)
      (launch_world files(Some physical_parent)task_traced_stop(Int64.repr 1048592)group)
| launch_continue:forall files group,
    actor=physical_parent ->
    launch_operation actor(launch_world files(Some physical_parent)task_traced_stop(Int64.repr 1048592)group)
      (process_traced(Int.repr 7)(Int.repr 2)(Vlong Int64.zero)(Vlong Int64.zero)Int64.zero)
      (launch_world files(Some physical_parent)task_running(Int64.repr 1048592)group)
| launch_close_ordinary:forall world fd reply,
    process_cgroup_files world actor fd=None ->
    launch_operation actor world(process_entry(entry_library(close_returned fd reply)))world.

Theorem launch_linux_contract:LinuxProcessContract launch_operation.
Proof.
  constructor.
  - intros before after parent child event OWN NONREAP OP.
    inversion OP;subst;try exact OWN;eapply launch_transport_owner;exact OWN.
  - intros before after parent event FRAME OP;inversion OP;subst;try reflexivity;
      discriminate FRAME.
  - intros before after parent child event OWN FRAME OP;inversion OP;subst;try reflexivity.
    destruct FRAME as[NONREAP OTHER];cbn[process_scope_frame_event process_machine_event launch_world]in OTHER.
    change(files parent(IO.descriptor q)=None)in OTHER.
    congruence.
  - intros before after parent child trace OWN OP;inversion OP;subst;try discriminate;
      split;[exact OWN|];split;reflexivity.
  - intros before after parent child OWN OP;inversion OP;subst;try discriminate;
      split;[exact OWN|];split;reflexivity.
  - intros before after parent child q reply OWN OP;inversion OP;subst;try discriminate.
    all:split;[eapply launch_transport_owner;exact OWN|reflexivity].
  - intros before after parent child q reply OWN OTHER OP;inversion OP;subst;try discriminate;try reflexivity.
    change(files parent(IO.descriptor q)=None)in OTHER.
    congruence.
  - intros before after parent child status offset word OWN OP STOP SIGNAL;inversion OP;subst;try discriminate.
    destruct(launch_owner_unique _ _ _ _ _ _ _ OWN)as[PARENT CHILD];subst;apply launch_stopped.
  - intros before after parent child status offset OWN OP;inversion OP;subst;try discriminate.
  - intros before after parent q bytes error group WRITING FILE OP;inversion OP;subst;try discriminate.
    + change(files parent(IO.descriptor q)=Some group)in FILE;congruence.
    + assumption.
  - intros before after parent child q bytes error group OWN WRITING FILE CANON OP;inversion OP;subst;try discriminate.
    + change(files parent(IO.descriptor q)=Some group)in FILE;congruence.
    + destruct(launch_owner_unique _ _ _ _ _ _ _ OWN)as[PARENT CHILD];subst.
      split;[apply launch_owns|].
      change(files physical_parent(IO.descriptor q)=Some group)in FILE.
      change(Some assigned=Some group);congruence.
  - intros before after parent child options OWN OP;inversion OP;subst;try discriminate.
    destruct(launch_owner_unique _ _ _ _ _ _ _ OWN)as[PARENT CHILD];subst.
    split;[apply launch_stopped|];split;[apply launch_stopped|];split;reflexivity.
  - intros before after parent child OWN OP;inversion OP;subst;try discriminate.
    destruct(launch_owner_unique _ _ _ _ _ _ _ OWN)as[PARENT CHILD];subst.
    split;[apply launch_stopped|]. split;[apply launch_owns|]. repeat split;reflexivity.
Qed.

(* The useful witness chooses no interference between its sampled operations.
   This chain retains every actual before/after world for the recording adapter. *)
Inductive LaunchSteps(actor:TaskIdentity):ProcessWorld->list process_event->ProcessWorld->Prop:=
| launch_steps_done:forall world,LaunchSteps actor world[]world
| launch_steps_next:forall before event middle events after,
    launch_operation actor before event middle ->LaunchSteps actor middle events after ->
    LaunchSteps actor before(event::events)after.

Theorem launch_steps_physical actor child before events after:
  LaunchSteps actor before events after ->process_world_steps launch_operation actor child before events after.
Proof.
  intro RUN;induction RUN;[constructor|].
  econstructor;[apply physical_no_interference|exact H|exact IHRUN].
Qed.

Theorem launch_steps_append actor before prefix middle suffix after:
  LaunchSteps actor before prefix middle ->LaunchSteps actor middle suffix after ->
  LaunchSteps actor before(prefix++suffix)after.
Proof.
  intro PREFIX;induction PREFIX;intro SUFFIX;[exact SUFFIX|].
  cbn;econstructor;[exact H|apply IHPREFIX;exact SUFFIX].
Qed.

Definition launch_empty_files:TaskIdentity->int->option nat:=fun _ _=>None.

Definition launch_parent_files:TaskIdentity->int->option nat:=fun actor fd=>
  if launch_task_eq actor physical_parent&&Int.eq fd(Int.repr 7)then Some 1%nat else None.
Definition launch_fork_files:TaskIdentity->int->option nat:=fun actor fd=>
  if (launch_task_eq actor physical_parent||launch_task_eq actor physical_child)&&Int.eq fd(Int.repr 7)
    then Some 1%nat else None.

Lemma launch_parent_file:launch_parent_files physical_parent(Int.repr 7)=Some 1%nat.
Proof. unfold launch_parent_files;rewrite launch_task_eq_same,Int.eq_true;reflexivity. Qed.

Lemma launch_parent_close_drops_files:
  launch_close_files launch_parent_files physical_parent(Int.repr 7)=launch_empty_files.
Proof.
  apply functional_extensionality;intro actor;apply functional_extensionality;intro fd.
  unfold launch_close_files,launch_parent_files,launch_empty_files.
  destruct(launch_task_eq actor physical_parent&&Int.eq fd(Int.repr 7));reflexivity.
Qed.

Lemma launch_child_exec_drops_copied_file:launch_exec_files launch_fork_files physical_child=launch_parent_files.
Proof.
  apply functional_extensionality;intro actor;apply functional_extensionality;intro fd.
  unfold launch_exec_files,launch_fork_files,launch_parent_files.
  destruct(launch_task_eq actor physical_child)eqn:CHILD.
  - apply launch_task_eq_sound in CHILD;subst actor.
    change(None=(if false&&Int.eq fd(Int.repr 7)then Some 1%nat else None));reflexivity.
  - rewrite orb_false_r;reflexivity.
Qed.

Definition launch_before_fork:ProcessWorld:={|
  process_pid:=fun _=>None;
  process_tasks:=fun _=>{|owned_parent:=physical_parent;owned_phase:=task_running;
    owned_tracer:=None;owned_options:=Int64.zero;owned_cgroup:=None|};
  process_cgroup_files:=launch_parent_files;
  process_explicit_reap:=fun _=>true;process_sole_waiter:=fun _=>true|}.

Theorem launch_same_fork_process namespace snapshot:
  NamespaceKernel.fork_matches namespace snapshot ->
  fork_parent snapshot=physical_parent ->fork_child snapshot=physical_child ->
  ForkProcessEffect namespace launch_before_fork snapshot
    (launch_world launch_fork_files None task_running Int64.zero None).
Proof.
  intros MATCH PARENT CHILD;constructor;try exact MATCH.
  - reflexivity.
  - rewrite CHILD;unfold launch_world,physical_child;cbn;rewrite Int.eq_true;reflexivity.
  - rewrite PARENT,CHILD;reflexivity.
  - intros;reflexivity.
  - reflexivity.
  - rewrite PARENT;apply functional_extensionality;intro fd.
    change(launch_fork_files physical_parent fd=launch_parent_files physical_parent fd).
    unfold launch_fork_files,launch_parent_files;rewrite launch_task_eq_same;reflexivity.
Qed.

(* These are separate child kernel effects. The tracing stop is committed
   before the parent wait; its eventual FFI return may follow the resume. *)
Inductive LaunchChildEffect:ProcessWorld->nat->ProcessWorld->Prop:=
| launch_worker_trace:forall files group,
    LaunchChildEffect(launch_world files None task_running Int64.zero group)2
      (launch_world files(Some physical_parent)task_running Int64.zero group)
| launch_worker_stop:forall files options group,
    LaunchChildEffect(launch_world files(Some physical_parent)task_running options group)3
      (launch_world files(Some physical_parent)task_traced_stop options group)
| launch_worker_frame:forall files tracer phase options group code,
    code<>2%nat ->code<>3%nat ->code<>24%nat ->
    LaunchChildEffect(launch_world files tracer phase options group)code
      (launch_world files tracer phase options group).

Theorem launch_worker_establishes_actual_stop:
  LaunchChildEffect(launch_world launch_parent_files None task_running Int64.zero None)2
    (launch_world launch_parent_files(Some physical_parent)task_running Int64.zero None) /\
  LaunchChildEffect(launch_world launch_parent_files(Some physical_parent)task_running Int64.zero None)3
    (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None) /\
  OwnsStopped(launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)
    physical_parent physical_child.
Proof. split;[constructor|]. split;[constructor|apply launch_stopped]. Qed.

Lemma launch_close_empty actor fd:launch_close_files launch_empty_files actor fd=launch_empty_files.
Proof.
  apply functional_extensionality;intro task;apply functional_extensionality;intro descriptor.
  unfold launch_close_files,launch_empty_files;destruct(launch_task_eq task actor&&Int.eq descriptor fd);reflexivity.
Qed.

Lemma launch_library_live_operation ge cell before event after actor tracer phase options group:
  library_step ge cell(live before)event(live after) ->
  launch_operation actor(launch_world launch_empty_files tracer phase options group)
    (process_entry(entry_library event))(launch_world launch_empty_files tracer phase options group).
Proof.
  intro STEP;inversion STEP;subst;try solve[apply launch_neutral;reflexivity].
  - match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>inversion ORIGINAL;subst end;
      try solve[apply launch_neutral;reflexivity].
    apply launch_io;reflexivity.
  - pose proof(launch_close actor launch_empty_files tracer phase options group fd reply)as CLOSE.
    rewrite launch_close_empty in CLOSE;exact CLOSE.
Qed.

Theorem launch_live_library_steps ge cell before events after actor tracer phase options group:
  library_steps ge cell(live before)events(live after) ->
  LaunchSteps actor
    (launch_world launch_empty_files tracer phase options group)
    (map(fun event=>process_entry(entry_library event))events)
    (launch_world launch_empty_files tracer phase options group).
Proof.
  revert before after;induction events as[|event events IH];intros before after RUN.
  - constructor.
  - inversion RUN as[|first head middle tail final STEP REST];subst.
    destruct middle as[middle|memory].
    + econstructor;[eapply launch_library_live_operation;exact STEP|].
      eapply IH;exact REST.
    + destruct(library_dead_steps _ _ _ _ _ REST)as[EMPTY IMPOSSIBLE];discriminate.
Qed.

Theorem launch_live_library_trace ge cell before events after actor child tracer phase options group:
  library_steps ge cell(live before)events(live after) ->
  process_world_steps launch_operation actor child
    (launch_world launch_empty_files tracer phase options group)
    (map(fun event=>process_entry(entry_library event))events)
    (launch_world launch_empty_files tracer phase options group).
Proof. intro RUN;apply launch_steps_physical;eapply launch_live_library_steps;exact RUN. Qed.

Lemma launch_passive_steps actor files tracer phase options group events:
  Forall(fun event=>launch_passive event=true)events ->
  LaunchSteps actor(launch_world files tracer phase options group)events
    (launch_world files tracer phase options group).
Proof.
  intro EVENTS;induction EVENTS;[constructor|].
  econstructor;[apply launch_neutral;exact H|exact IHEVENTS].
Qed.

Lemma launch_passive_trace actor child files tracer phase options group events:
  Forall(fun event=>launch_passive event=true)events ->
  process_world_steps launch_operation actor child(launch_world files tracer phase options group)events
    (launch_world files tracer phase options group).
Proof.
  intro EVENTS;apply launch_steps_physical,launch_passive_steps;exact EVENTS.
Qed.

Lemma launch_source_repeat count:Forall(fun event=>launch_passive event=true)(repeat process_source_event count).
Proof. induction count;cbn;constructor;auto. Qed.

Lemma launch_pid2_canonical:canonical_pid[Byte.repr 50]physical_child.
Proof.
  split;[constructor;[change(48<=50<=57);lia|constructor]|]. split.
  - exists(Byte.repr 50),[];split;[reflexivity|vm_compute;discriminate].
  - vm_compute;reflexivity.
Qed.

Theorem launch_admission_steps files cell locals status first second group:
  files physical_parent(Int.repr 7)=Some 1%nat ->
  LaunchSteps physical_parent
    (launch_world files(Some physical_parent)task_traced_stop Int64.zero group)
    (physical_admission_events cell locals(Int.repr 7)status first second)
    (launch_world files(Some physical_parent)task_traced_stop(Int64.repr 1048592)(Some 1%nat)).
Proof.
  intro FILE;unfold physical_admission_events.
  eapply launch_steps_append;[apply launch_passive_steps,launch_source_repeat|].
  econstructor;[apply launch_wait_stop;try reflexivity|].
  eapply launch_steps_append;[apply launch_passive_steps,launch_source_repeat|].
  econstructor;[apply launch_neutral;reflexivity|].
  eapply launch_steps_append;[apply launch_passive_steps,launch_source_repeat|].
  econstructor;[eapply launch_place;
    [exact FILE|reflexivity|reflexivity|apply launch_pid2_canonical]|].
  eapply launch_steps_append;[apply launch_passive_steps,launch_source_repeat|].
  econstructor;[apply launch_options;reflexivity|].
  apply launch_passive_steps,launch_source_repeat.
Qed.

Theorem launch_admission_trace files cell locals status first second group:
  files physical_parent(Int.repr 7)=Some 1%nat ->
  process_world_steps launch_operation physical_parent physical_child
    (launch_world files(Some physical_parent)task_traced_stop Int64.zero group)
    (physical_admission_events cell locals(Int.repr 7)status first second)
    (launch_world files(Some physical_parent)task_traced_stop(Int64.repr 1048592)(Some 1%nat)).
Proof. intro FILE;apply launch_steps_physical,launch_admission_steps;exact FILE. Qed.

(* The source event list is exactly the one executed in the physical model. *)
Theorem launch_actual_source_admission files cell before status error group:
  files physical_parent(Int.repr 7)=Some 1%nat ->
  initialized_errno cell before error ->Mem.valid_access before Mint32 status 0 Writable ->status<>tls_block cell ->
  exists locals first second after,
    process_steps admission_ge cell
      (live(Callstate(Internal EntrySource.f_admit_child)
        [Vint(Int.repr 2);Vint(Int.repr 7);Vptr status Ptrofs.zero]Kstop before))
      (physical_admission_events cell locals(Int.repr 7)status first second)
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    process_world_steps launch_operation physical_parent physical_child
      (launch_world files(Some physical_parent)task_traced_stop Int64.zero group)
      (physical_admission_events cell locals(Int.repr 7)status first second)
      (launch_world files(Some physical_parent)task_traced_stop(Int64.repr 1048592)(Some 1%nat)).
Proof.
  intros FILE ERRNO ACCESS SEPARATE.
  destruct(actual_useful_admission_has_physical_execution cell before(Int.repr 7)status error ERRNO ACCESS SEPARATE)
    as[locals[first[second[after[SOURCE PHYSICAL]]]]].
  exists locals,first,second,after;split;[exact SOURCE|apply launch_admission_trace;exact FILE].
Qed.

Lemma launch_return_path_passive ge cell(P:mem->Prop)start count value memory events actual after:
  store_path ge P start count(Returnstate value Kstop memory) ->
  process_steps ge cell(live start)events(live(Returnstate actual Kstop after)) ->
  Forall(fun event=>launch_passive event=true)events.
Proof.
  intros PATH RUN.
  destruct(process_store_path_decomposition _ _ _ _ _ _ PATH _ _ RUN)
    as[[rest[EVENTS TAIL]]|[[used[current[remaining[COUNT[EVENTS[TARGET TAIL]]]]]]|
      [used[dead_memory[COUNT[EVENTS[TARGET PRESERVED]]]]]]];[| |discriminate].
  - destruct(process_terminal_run_constant _ _ _ _ _ _ _ TAIL)as[EMPTY REST];subst rest.
    rewrite EVENTS,app_nil_r;apply launch_source_repeat.
  - rewrite EVENTS;apply launch_source_repeat.
Qed.

(* This property is proved over the real clock source, not supplied as a
   contract for the whole callback. Its possible return word is irrelevant. *)
Theorem launch_actual_clock_passive cell before events value after:
  entry_errno_ready cell before ->
  process_steps admission_ge cell(live(Callstate(Internal EntrySource.f_now_ms)[]Kstop before))events
    (live(Returnstate value Kstop after)) ->
  Forall(fun event=>launch_passive event=true)events.
Proof.
  intros[error[LOW[HIGH[ACCESS LOAD]]]]RUN.
  destruct(Mem.alloc before 0 16)as[allocated output]eqn:ALLOC.
  assert(VALID:Mem.valid_block before(tls_block cell)).
  { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(FRESH:~Mem.valid_block before output)by(eapply Mem.fresh_block_alloc;exact ALLOC).
  assert(SEPARATE:output<>tls_block cell)by congruence.
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (clock_start_to_call before allocated output Kstop ALLOC)ltac:(intros;discriminate)RUN)
    as[tail[EVENTS CONTINUE]].
  destruct(clock_return_decomposition _ _ _ _ _ _ _ _ _ _ CONTINUE)
    as[waiting[observation[memory[rest[RETURN[EFFECT[READY REST]]]]]]].
  assert(OWN:Mem.range_perm memory output 0 16 Cur Freeable).
  { intros position RANGE;apply(clock_effect_permissions _ _ _ _ _ _ EFFECT).
    eapply Mem.perm_alloc_2;[exact ALLOC|exact RANGE]. }
  destruct(clock_observation_source cell output allocated observation memory clock_temps Kstop SEPARATE EFFECT OWN)
    as[count[freed[BOUND[FREE PATH]]]].
  rewrite EVENTS,RETURN;apply Forall_app;split;[apply launch_source_repeat|].
  apply Forall_app;split.
  - apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst;reflexivity.
  - constructor;[reflexivity|]. eapply launch_return_path_passive;eassumption.
Qed.

Definition LaunchNamespaceSteps actor before events after:Prop:=
  exists originals,events=map namespace_process originals /\LaunchSteps actor before originals after.

Lemma launch_namespace_append actor before prefix middle suffix after:
  LaunchNamespaceSteps actor before prefix middle ->LaunchNamespaceSteps actor middle suffix after ->
  LaunchNamespaceSteps actor before(prefix++suffix)after.
Proof.
  intros[first[PREFIX LEFT]][second[SUFFIX RIGHT]].
  exists(first++second);split;[rewrite map_app,PREFIX,SUFFIX;reflexivity|].
  eapply launch_steps_append;eassumption.
Qed.

Lemma launch_quiet_namespace_steps actor files tracer phase options group counts:
  LaunchNamespaceSteps actor(launch_world files tracer phase options group)(namespace_quiet_trace counts)
    (launch_world files tracer phase options group).
Proof.
  exists(flat_map(repeat process_source_event)counts);split.
  - induction counts as[|count counts IH];[reflexivity|].
    change(repeat namespace_source_event count++namespace_quiet_trace counts=
      map namespace_process(repeat process_source_event count++flat_map(repeat process_source_event)counts)).
    rewrite map_app,map_repeat,<-IH;reflexivity.
  - apply launch_passive_steps;induction counts as[|count counts IH];[constructor|].
    cbn[flat_map];apply Forall_app;split;[apply launch_source_repeat|exact IH].
Qed.

(* The actual callback certificate fixes every active segment and its order.
   This useful world chain consumes those source segments at the same memory
   states, rather than choosing a separate successful admission or sender. *)
Theorem launch_actual_callback_steps cell memory status admission report sequence events
    (shape:NamespaceCallbackShape cell memory status admission report sequence events):
  LaunchNamespaceSteps physical_parent
    (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)events
    (launch_world launch_empty_files(Some physical_parent)task_traced_stop(Int64.repr 1048592)(Some 1%nat)).
Proof.
  rewrite(callback_event_order _ _ _ _ _ _ _ shape).
  eapply launch_namespace_append;[apply launch_quiet_namespace_steps|].
  eapply launch_namespace_append.
  { eexists;split;[reflexivity|apply launch_admission_steps,launch_parent_file]. }
  eapply launch_namespace_append;[apply launch_quiet_namespace_steps|].
  eapply launch_namespace_append.
  { exists[process_entry(entry_library(close_returned(Int.repr 7)(close_ok None)))];split;[reflexivity|].
    econstructor;[|constructor].
    pose proof(launch_close physical_parent launch_parent_files(Some physical_parent)task_traced_stop
      (Int64.repr 1048592)(Some 1%nat)(Int.repr 7)(close_ok None))as CLOSE.
    rewrite launch_parent_close_drops_files in CLOSE;exact CLOSE. }
  eapply launch_namespace_append;[apply launch_quiet_namespace_steps|].
  eapply launch_namespace_append.
  { eexists;split;[reflexivity|apply launch_passive_steps].
    eapply launch_actual_clock_passive;[exact(callback_clock_ready _ _ _ _ _ _ _ shape)|].
    exact(callback_clock_source _ _ _ _ _ _ _ shape). }
  eapply launch_namespace_append;[apply launch_quiet_namespace_steps|].
  eapply launch_namespace_append.
  { exists(map(fun event=>process_entry(entry_library event))(callback_sender_events _ _ _ _ _ _ _ shape)).
    split;[rewrite map_map;reflexivity|].
    eapply launch_live_library_steps;exact(callback_sender_source _ _ _ _ _ _ _ shape). }
  apply launch_quiet_namespace_steps.
Qed.

Theorem launch_release_steps request:
  LaunchSteps physical_parent
    (launch_world launch_empty_files(Some physical_parent)task_traced_stop(Int64.repr 1048592)(Some 1%nat))
    (release_useful_events(Int.repr 2)request)
    (launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1%nat)).
Proof.
  unfold release_useful_events.
  eapply launch_steps_append;[apply launch_passive_steps,launch_source_repeat|].
  econstructor;[apply launch_continue;reflexivity|].
  eapply launch_steps_append;[apply launch_passive_steps,launch_source_repeat|].
  eapply launch_steps_append;[apply launch_passive_steps,launch_source_repeat|].
  econstructor;[apply launch_io;reflexivity|].
  eapply launch_steps_append;[apply launch_passive_steps,launch_source_repeat|].
  apply launch_passive_steps,launch_source_repeat.
Qed.

Theorem launch_actual_source_release cell before:
  entry_errno_ready cell before ->
  exists events after request,
    process_steps admission_ge cell
      (live(Callstate(Internal EntrySource.f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]Kstop before))events
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    descriptor request=Int.repr 9 /\events=release_useful_events(Int.repr 2)request /\
    LaunchSteps physical_parent
      (launch_world launch_empty_files(Some physical_parent)task_traced_stop(Int64.repr 1048592)(Some 1%nat))events
      (launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1%nat)).
Proof.
  intro READY;destruct(release_useful_source_execution_shaped cell before(Int.repr 2)(Int.repr 9)READY)
    as[events[after[SOURCE[request[DESCRIPTOR[WRITE EVENTS]]]]]].
  exists events,after,request;split;[exact SOURCE|]. split;[exact DESCRIPTOR|].
  split;[exact EVENTS|rewrite EVENTS;apply launch_release_steps].
Qed.

Lemma launch_parent_close_other fd:fd<>Int.repr 7 ->
  launch_close_files launch_parent_files physical_parent fd=launch_parent_files.
Proof.
  intro OTHER;apply functional_extensionality;intro actor;apply functional_extensionality;intro query.
  unfold launch_close_files;destruct(launch_task_eq actor physical_parent&&Int.eq query fd)eqn:SELECTED;
    [|reflexivity].
  apply andb_true_iff in SELECTED as[ACTOR SLOT];apply Int.same_if_eq in SLOT;subst query.
  unfold launch_parent_files;rewrite Int.eq_false by exact OTHER.
  rewrite andb_false_r;reflexivity.
Qed.

Theorem launch_actual_parent_prefix_steps tracer phase options group events:
  Forall namespace_parent_prefix_event events ->
  LaunchNamespaceSteps physical_parent(launch_world launch_parent_files tracer phase options group)events
    (launch_world launch_parent_files tracer phase options group).
Proof.
  intro EVENTS;induction EVENTS.
  - exists[];split;[reflexivity|constructor].
  - apply launch_namespace_append with(prefix:=[x])(suffix:=l)
      (middle:=launch_world launch_parent_files tracer phase options group);[|exact IHEVENTS].
    destruct H as[SOURCE|[fd[MEMBER CLOSE]]];subst x.
    + exists[process_source_event];split;[reflexivity|]. econstructor;[apply launch_neutral;reflexivity|constructor].
    + exists[process_entry(entry_library(close_returned fd(close_ok None)))];split;[reflexivity|].
      econstructor;[|constructor].
      assert(OTHER:fd<>Int.repr 7).
      { cbn in MEMBER;repeat destruct MEMBER as[MEMBER|MEMBER];try contradiction;subst fd;vm_compute;discriminate. }
      pose proof(launch_close physical_parent launch_parent_files tracer phase options group fd(close_ok None))as STEP.
      rewrite launch_parent_close_other in STEP by exact OTHER;exact STEP.
Qed.

Theorem launch_same_source_parent_timeline cell e pair parameters before suffix final request
    (shape:NamespaceUsefulParentShape cell e pair parameters before suffix final request):
  LaunchNamespaceSteps physical_parent
    (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)suffix
    (launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1%nat)).
Proof.
  rewrite(useful_parent_event_order _ _ _ _ _ _ _ _ shape).
  eapply launch_namespace_append;[apply launch_actual_parent_prefix_steps;
    exact(useful_prefix_profile _ _ _ _ _ _ _ _ shape)|].
  eapply launch_namespace_append.
  { exact(launch_actual_callback_steps _ _ _ _ _ _ _ (useful_callback_shape _ _ _ _ _ _ _ _ shape)). }
  exists(useful_release_events _ _ _ _ _ _ _ _ shape);split;[reflexivity|].
  rewrite(useful_release_shape _ _ _ _ _ _ _ _ shape);apply launch_release_steps.
Qed.

Lemma launch_passive_is_namespace_passive event:
  launch_passive event=true ->namespace_passive_event(namespace_process event)=true.
Proof.
  intro PASSIVE;destruct event;try reflexivity;try discriminate.
  repeat match goal with
  |H:launch_passive(process_entry(entry_library ?library))=true|-_=>is_var library;
    destruct library;try reflexivity;try discriminate
  |H:launch_passive(process_entry ?entry)=true|-_=>is_var entry;
    destruct entry;try reflexivity;try discriminate
  end.
Qed.

Theorem launch_operation_has_namespace_step actor before event after namespace:
  launch_operation actor before event after ->
  exists next,namespace_kernel_event namespace(namespace_process event)next.
Proof.
  intro OP;destruct OP.
  - exists namespace;apply namespace_kernel_passive,launch_passive_is_namespace_passive;exact H.
  - exists namespace;apply namespace_kernel_passive;reflexivity.
  - exists(namespace_retable namespace(table_remove(namespace_table namespace)fd)).
    apply namespace_kernel_close;destruct reply;constructor.
  - exists(namespace_exec namespace default_signal_action);apply namespace_kernel_exec.
    unfold namespace_exec_action;intros;reflexivity.
  - destruct H as[ZERO|ONE];subst flags;eexists;[apply namespace_kernel_flags_zero|apply namespace_kernel_flags_one].
  - exists namespace;apply namespace_kernel_passive;reflexivity.
  - exists namespace;apply namespace_kernel_passive;reflexivity.
  - exists namespace;apply namespace_kernel_passive;reflexivity.
  - exists namespace;apply namespace_kernel_passive;reflexivity.
  - exists(namespace_retable namespace(table_remove(namespace_table namespace)fd)).
    apply namespace_kernel_close;destruct reply;constructor.
Qed.

Inductive LaunchNamespaceRecording(actor:TaskIdentity):
    ProcessWorld->NamespaceWorld->list process_event->ProcessWorld->NamespaceWorld->Prop:=
| launch_namespace_done:forall process namespace,LaunchNamespaceRecording actor process namespace[]process namespace
| launch_namespace_next:forall before namespace event middle next events after final,
    launch_operation actor before event middle ->namespace_kernel_event namespace(namespace_process event)next ->
    LaunchNamespaceRecording actor middle next events after final ->
    LaunchNamespaceRecording actor before namespace(event::events)after final.

Theorem launch_steps_have_namespace_recording actor before events after:
  LaunchSteps actor before events after ->forall namespace,
    exists final,LaunchNamespaceRecording actor before namespace events after final.
Proof.
  intro RUN;induction RUN;intro namespace;[exists namespace;constructor|].
  destruct(launch_operation_has_namespace_step _ _ _ _ namespace H)as[next KERNEL].
  destruct(IHRUN next)as[final REST];exists final;econstructor;eassumption.
Qed.

Theorem launch_recording_namespace_kernel actor before namespace events after final:
  LaunchNamespaceRecording actor before namespace events after final ->
  namespace_kernel_steps namespace(map namespace_process events)final.
Proof. intro RUN;induction RUN;cbn;[constructor|econstructor;eassumption]. Qed.

Lemma launch_file_view_flags groups world actor namespace fd flag:
  SourceFileView groups world actor namespace ->
  SourceFileView groups world actor(namespace_retable namespace(descriptor_flags(namespace_table namespace)fd flag)).
Proof.
  intros VIEW query group;split.
  - intro FILE;destruct(proj1(VIEW query group)FILE)as[binding[object[PRESENT[OBJECT CLASS]]]].
    unfold descriptor_flags.
    change(exists next object, (match namespace_table namespace query with
      |Some previous=>if Int.eq query fd then
        Some{|descriptor_object:=descriptor_object previous;descriptor_cloexec:=flag|}else Some previous
      |None=>None end)=Some next /\descriptor_object next=ordinary_object object /\groups object=Some group).
    rewrite PRESENT;destruct(Int.eq query fd);
      (eexists;exists object;split;[reflexivity|split;assumption]).
  - intros[binding[object[PRESENT[OBJECT CLASS]]]].
    change(descriptor_flags(namespace_table namespace)fd flag query=Some binding)in PRESENT.
    destruct(flags_preserve_object _ _ _ _ _ PRESENT)as[previous[OLD SAME]].
    apply(proj2(VIEW query group));exists previous,object;split;[exact OLD|]. split;[congruence|exact CLASS].
Qed.

Definition launch_not_image event:=match event with process_entry(entry_image _ _ _)=>False|_=>True end.

Theorem launch_operation_file_recording groups actor before event after namespace:
  launch_operation actor before event after ->launch_not_image event ->
  SourceFileView groups before actor namespace ->
  exists next,namespace_kernel_event namespace(namespace_process event)next /\
    SourceFileView groups after actor next.
Proof.
  intros OP NOIMAGE VIEW;destruct OP.
  - exists namespace;split;[apply namespace_kernel_passive,launch_passive_is_namespace_passive;exact H|exact VIEW].
  - exists namespace;split;[apply namespace_kernel_passive;reflexivity|exact VIEW].
  - exists(namespace_retable namespace(table_remove(namespace_table namespace)fd));split.
    + apply namespace_kernel_close;destruct reply;constructor.
    + intros query assigned;change(launch_close_files files actor fd actor query=Some assigned <->
        exists binding object,table_remove(namespace_table namespace)fd query=Some binding /\
          descriptor_object binding=ordinary_object object /\groups object=Some assigned).
      unfold launch_close_files,table_remove;rewrite launch_task_eq_same;cbn[andb].
      destruct(Int.eq query fd).
      * split;[discriminate|intros[binding[object[PRESENT REST]]];discriminate].
      * exact(VIEW query assigned).
  - contradiction.
  - destruct H as[ZERO|ONE];subst flags.
    + exists(namespace_retable namespace(descriptor_flags(namespace_table namespace)fd false));split;
        [apply namespace_kernel_flags_zero|apply launch_file_view_flags;exact VIEW].
    + exists(namespace_retable namespace(descriptor_flags(namespace_table namespace)fd true));split;
        [apply namespace_kernel_flags_one|apply launch_file_view_flags;exact VIEW].
  - exists namespace;split;[apply namespace_kernel_passive;reflexivity|exact VIEW].
  - exists namespace;split;[apply namespace_kernel_passive;reflexivity|exact VIEW].
  - exists namespace;split;[apply namespace_kernel_passive;reflexivity|exact VIEW].
  - exists namespace;split;[apply namespace_kernel_passive;reflexivity|exact VIEW].
  - exists(namespace_retable namespace(table_remove(namespace_table namespace)fd));split.
    + apply namespace_kernel_close;destruct reply;constructor.
    + intros query assigned;change(process_cgroup_files world actor query=Some assigned <->
        exists binding object,table_remove(namespace_table namespace)fd query=Some binding /\
          descriptor_object binding=ordinary_object object /\groups object=Some assigned).
      unfold table_remove;destruct(Int.eq query fd)eqn:SAME.
      * apply Int.same_if_eq in SAME;subst query;rewrite H;split;
          [discriminate|intros[binding[object[PRESENT REST]]];discriminate].
      * exact(VIEW query assigned).
Qed.

Inductive LaunchFileRecording groups(actor:TaskIdentity):
    ProcessWorld->NamespaceWorld->list process_event->ProcessWorld->NamespaceWorld->Prop:=
| launch_file_done:forall process namespace,
    SourceFileView groups process actor namespace ->LaunchFileRecording groups actor process namespace[]process namespace
| launch_file_next:forall before namespace event middle next events after final,
    SourceFileView groups before actor namespace ->launch_operation actor before event middle ->
    namespace_kernel_event namespace(namespace_process event)next ->
    LaunchFileRecording groups actor middle next events after final ->
    LaunchFileRecording groups actor before namespace(event::events)after final.

Theorem launch_steps_have_file_recording groups actor before events after:
  LaunchSteps actor before events after ->Forall launch_not_image events ->forall namespace,
    SourceFileView groups before actor namespace ->
    exists final,LaunchFileRecording groups actor before namespace events after final.
Proof.
  intro RUN;induction RUN;intros EVENTS namespace VIEW.
  - exists namespace;constructor;exact VIEW.
  - inversion EVENTS;subst.
    destruct(launch_operation_file_recording _ _ _ _ _ _ H H2 VIEW)as[next[KERNEL NEXT]].
    destruct(IHRUN H3 next NEXT)as[final REST];exists final;econstructor;eassumption.
Qed.

Lemma launch_passive_not_image event:launch_passive event=true ->launch_not_image event.
Proof. intro PASSIVE;destruct event;try exact I;destruct event;try exact I;discriminate. Qed.

Definition launch_namespace_not_image event:=match event with
  |namespace_process original=>launch_not_image original|_=>False end.

Lemma launch_map_not_image events:
  Forall launch_not_image events ->Forall launch_namespace_not_image(map namespace_process events).
Proof. intro EVENTS;induction EVENTS;cbn;constructor;assumption. Qed.

Lemma launch_map_not_image_back events:
  Forall launch_namespace_not_image(map namespace_process events) ->Forall launch_not_image events.
Proof. induction events;intro EVENTS;[constructor|inversion EVENTS;constructor;auto]. Qed.

Lemma launch_quiet_not_image counts:Forall launch_namespace_not_image(namespace_quiet_trace counts).
Proof.
  induction counts;[constructor|];change(Forall launch_namespace_not_image
    (repeat namespace_source_event a++namespace_quiet_trace counts)).
  apply Forall_app;split;[|exact IHcounts].
  apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst;exact I.
Qed.

Ltac launch_finite_no_image:=repeat first[
  match goal with |-Forall _ (?prefix++?suffix)=>apply Forall_app;split end|
  match goal with |-Forall _ (repeat ?event ?count)=>apply Forall_forall;intros actual MEMBER;
    apply repeat_spec in MEMBER;subst actual;exact I end|
  match goal with |-Forall _ []=>constructor end|
  match goal with |-Forall _ (?event::?events)=>constructor;[exact I|]end].

Lemma launch_admission_not_image cell locals status first second:
  Forall launch_not_image(physical_admission_events cell locals(Int.repr 7)status first second).
Proof. unfold physical_admission_events;launch_finite_no_image. Qed.

Lemma launch_release_not_image request:Forall launch_not_image(release_useful_events(Int.repr 2)request).
Proof. unfold release_useful_events;launch_finite_no_image. Qed.

Lemma launch_callback_not_image cell memory status admission report sequence events
    (shape:NamespaceCallbackShape cell memory status admission report sequence events):
  Forall launch_namespace_not_image events.
Proof.
  rewrite(callback_event_order _ _ _ _ _ _ _ shape).
  apply Forall_app;split;[apply launch_quiet_not_image|].
  apply Forall_app;split;[apply launch_map_not_image,launch_admission_not_image|].
  apply Forall_app;split;[apply launch_quiet_not_image|].
  apply Forall_app;split;[constructor;[exact I|constructor]|].
  apply Forall_app;split;[apply launch_quiet_not_image|].
  apply Forall_app;split.
  - apply launch_map_not_image;apply Forall_forall;intros event MEMBER;apply launch_passive_not_image.
    pose proof(launch_actual_clock_passive _ _ _ _ _(callback_clock_ready _ _ _ _ _ _ _ shape)
      (callback_clock_source _ _ _ _ _ _ _ shape))as EVENTS.
    rewrite Forall_forall in EVENTS;apply EVENTS;exact MEMBER.
  - apply Forall_app;split;[apply launch_quiet_not_image|].
    apply Forall_app;split;[|apply launch_quiet_not_image].
    apply Forall_forall;intros event MEMBER;apply in_map_iff in MEMBER;destruct MEMBER as[original[SAME MEMBER]].
    subst event;exact I.
Qed.

Theorem launch_same_parent_events_not_image cell e pair parameters before suffix final request
    (shape:NamespaceUsefulParentShape cell e pair parameters before suffix final request):
  Forall launch_namespace_not_image suffix.
Proof.
  rewrite(useful_parent_event_order _ _ _ _ _ _ _ _ shape).
  apply Forall_app;split.
  - pose proof(useful_prefix_profile _ _ _ _ _ _ _ _ shape)as PREFIX.
    rewrite Forall_forall in PREFIX;apply Forall_forall;intros event MEMBER.
    destruct(PREFIX _ MEMBER)as[SOURCE|[fd[SELECTED CLOSE]]];subst event;exact I.
  - apply Forall_app;split.
    + exact(launch_callback_not_image _ _ _ _ _ _ _(useful_callback_shape _ _ _ _ _ _ _ _ shape)).
    + rewrite(useful_release_shape _ _ _ _ _ _ _ _ shape);apply launch_map_not_image,launch_release_not_image.
Qed.

Theorem launch_same_source_parent_file_timeline groups cell e pair parameters before suffix final request
    (shape:NamespaceUsefulParentShape cell e pair parameters before suffix final request) namespace:
  SourceFileView groups(launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)
    physical_parent namespace ->
  exists originals after,suffix=map namespace_process originals /\
    LaunchFileRecording groups physical_parent
      (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)namespace originals
      (launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1%nat))after.
Proof.
  intro VIEW;destruct(launch_same_source_parent_timeline _ _ _ _ _ _ _ _ shape)as[originals[EVENTS RUN]].
  pose proof(launch_same_parent_events_not_image _ _ _ _ _ _ _ _ shape)as NOIMAGE.
  rewrite EVENTS in NOIMAGE;apply launch_map_not_image_back in NOIMAGE.
  destruct(launch_steps_have_file_recording _ _ _ _ _ RUN NOIMAGE namespace VIEW)as[after RECORDING].
  exists originals,after;split;assumption.
Qed.

Definition launch_group_objects object:option nat:=if Nat.eqb object 103 then Some 1%nat else None.

Lemma launch_fork_cgroup_present:
  namespace_table fork_fixture_world(Int.repr 7)=
    Some{|descriptor_object:=ordinary_object 103;descriptor_cloexec:=true|}.
Proof. vm_compute;reflexivity. Qed.

Lemma launch_fork_cgroup_unique fd binding:
  namespace_table fork_fixture_world fd=Some binding ->descriptor_object binding=ordinary_object 103 ->fd=Int.repr 7.
Proof.
  intros PRESENT OBJECT;change(fork_fixture_inherited fd=Some binding)in PRESENT.
  unfold fork_fixture_inherited,fork_fixture_duplicated,fork_fixture_paired,table_remove,table_put in PRESENT.
  destruct(Int.eq fd(Int.repr 10));[discriminate|].
  destruct(Int.eq fd(Int.repr 60));[inversion PRESENT;subst;discriminate OBJECT|].
  destruct(Int.eq fd(Int.repr 9));[inversion PRESENT;subst;discriminate OBJECT|].
  unfold fork_fixture_ordinary in PRESENT.
  destruct(Z.leb 0(Int.signed fd)&&Z.leb(Int.signed fd)8)eqn:BOUNDS;[|discriminate].
  inversion PRESENT;subst binding;cbn[descriptor_object]in OBJECT.
  destruct(Int.eq fd Int.zero||Int.eq fd(Int.repr 2));[discriminate|].
  injection OBJECT as NUMBER.
  apply andb_true_iff in BOUNDS as[LOW HIGH];apply Z.leb_le in LOW,HIGH.
  assert(SIGNED:Int.signed fd=7).
  { assert(SMALL:Z.to_nat(Int.signed fd)=7%nat)by lia.
    apply(f_equal Z.of_nat)in SMALL;rewrite Z2Nat.id in SMALL by exact LOW;exact SMALL. }
  rewrite <-(Int.repr_signed fd),SIGNED;reflexivity.
Qed.

Theorem launch_actual_fork_file_view:
  SourceFileView launch_group_objects
    (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)
    physical_parent fork_fixture_world.
Proof.
  intros fd group;change(launch_parent_files physical_parent fd=Some group <->
    exists binding object,namespace_table fork_fixture_world fd=Some binding /\
      descriptor_object binding=ordinary_object object /\launch_group_objects object=Some group).
  unfold launch_parent_files;rewrite launch_task_eq_same;cbn[andb];split.
  - destruct(Int.eq fd(Int.repr 7))eqn:SELECTED;[|discriminate].
    intro FILE;inversion FILE;subst group;apply Int.same_if_eq in SELECTED;subst fd.
    exists{|descriptor_object:=ordinary_object 103;descriptor_cloexec:=true|},103%nat.
    split;[apply launch_fork_cgroup_present|]. split;reflexivity.
  - intros[binding[object[PRESENT[OBJECT CLASS]]]].
    unfold launch_group_objects in CLASS;destruct(Nat.eqb object 103)eqn:SELECTED;[|discriminate].
    apply Nat.eqb_eq in SELECTED;subst object;inversion CLASS;subst group.
    pose proof(launch_fork_cgroup_unique _ _ PRESENT OBJECT)as SAME;subst fd;rewrite Int.eq_true;reflexivity.
Qed.

Theorem launch_actual_parent_file_timeline cell e pair parameters before suffix final request
    (shape:NamespaceUsefulParentShape cell e pair parameters before suffix final request):
  exists originals after,suffix=map namespace_process originals /\
    LaunchFileRecording launch_group_objects physical_parent
      (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)
      fork_fixture_world originals
      (launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1%nat))after.
Proof.
  exact(launch_same_source_parent_file_timeline _ _ _ _ _ _ _ _ _ shape _ launch_actual_fork_file_view).
Qed.

Definition launch_nonnegative_table(table:DescriptorTable):=forall fd binding,table fd=Some binding ->0<=Int.signed fd.

Lemma launch_namespace_nonnegative before event after:
  namespace_kernel_event before(namespace_process event)after ->
  launch_nonnegative_table(namespace_table before) ->launch_nonnegative_table(namespace_table after).
Proof.
  intros STEP NONNEGATIVE fd binding PRESENT.
  destruct(namespace_process_object_frame _ _ _ STEP _ _ PRESENT)as[previous[OLD SAME]].
  eapply NONNEGATIVE;exact OLD.
Qed.

Theorem launch_actual_fork_nonnegative:launch_nonnegative_table(namespace_table fork_fixture_world).
Proof.
  intros fd binding PRESENT;change(fork_fixture_inherited fd=Some binding)in PRESENT.
  unfold fork_fixture_inherited,fork_fixture_duplicated,fork_fixture_paired,table_remove,table_put in PRESENT.
  destruct(Int.eq fd(Int.repr 10));[discriminate|].
  destruct(Int.eq fd(Int.repr 60))eqn:SIXTY.
  - apply Int.same_if_eq in SIXTY;subst fd;change(0<=60);lia.
  - destruct(Int.eq fd(Int.repr 9))eqn:NINE.
    + apply Int.same_if_eq in NINE;subst fd;change(0<=9);lia.
    + unfold fork_fixture_ordinary in PRESENT.
      destruct(Z.leb 0(Int.signed fd)&&Z.leb(Int.signed fd)8)eqn:BOUNDS;[|discriminate].
      apply andb_true_iff in BOUNDS as[LOW HIGH];apply Z.leb_le;exact LOW.
Qed.
