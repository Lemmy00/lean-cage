(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Inhabit the physical admission contracts with an actual useful source trace. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine ErrorNumber.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessStatus ProcessOwnership ProcessPhysicalTrace ProcessPaths.
From EntryProcess Require Import ProcessAdmissionWitness ProcessAdmissionPhysical ProcessStructure ProcessPlacement ProcessAllocation.
From EntryProcess Require Import ProcessAdmissionNonvacuity.
From EntryNamespace Require Import NamespaceObjects.
Import ListNotations.
Open Scope Z_scope.

Definition physical_parent : TaskIdentity := {|task_pid:=Int.one;task_incarnation:=0|}.
Definition physical_child : TaskIdentity := {|task_pid:=Int.repr 2;task_incarnation:=0|}.

(* This is a useful primitive-model instance, not a restriction on the broader
   source or Linux relations quantified by the admission theorem. All identity,
   placement and tracing laws below are proved for its explicit states. *)
Definition physical_world cgroup phase options group : ProcessWorld :=
  {|process_pid:=fun pid=>if Int.eq pid(Int.repr 2)then Some physical_child else None;
    process_tasks:=fun _=>{|owned_parent:=physical_parent;owned_phase:=phase;
      owned_tracer:=Some physical_parent;owned_options:=options;owned_cgroup:=group|};
    process_cgroup_files:=fun _ fd=>if Int.eq fd cgroup then Some 1%nat else None;
    process_explicit_reap:=fun _=>true;process_sole_waiter:=fun _=>true|}.

Definition physical_passive event :=
  match event with
  |process_entry(entry_library(original_event(source_step _)))
  |process_entry(entry_library(original_event errno_step))
  |process_entry(entry_formatted _ _ _ _)
  |process_entry entry_primitive_wait|process_waiting=>true
  |_=>false
  end.

Inductive physical_operation cgroup (actor:TaskIdentity) : ProcessWorld->process_event->ProcessWorld->Prop :=
| physical_neutral : forall phase options group event,
    physical_passive event=true ->
    physical_operation cgroup actor(physical_world cgroup phase options group)event
      (physical_world cgroup phase options group)
| physical_wait_stop : forall phase options group status offset word,
    admission_is_stopped word=true ->admission_is_sigstop word=true ->
    physical_operation cgroup actor(physical_world cgroup phase options group)
      (process_waited(Int.repr 2)status offset Int.zero(wait_status(Int.repr 2)word))
      (physical_world cgroup task_traced_stop options group)
| physical_wait_interrupt : forall phase options group status offset,
    physical_operation cgroup actor(physical_world cgroup phase options group)
      (process_waited(Int.repr 2)status offset Int.zero(wait_failed(Int.repr 4)))
      (physical_world cgroup phase options group)
| physical_place : forall phase options group q bytes error,
    IO.operation q=writing ->IO.descriptor q=cgroup ->
    Z.of_nat(length bytes)=requested q ->canonical_pid bytes physical_child ->
    physical_operation cgroup actor(physical_world cgroup phase options group)
      (process_machine_event(io_step q(transfer bytes error)))
      (physical_world cgroup phase options(Some 1%nat))
| physical_options : forall options group next,
    physical_operation cgroup actor(physical_world cgroup task_traced_stop options group)
      (process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)(Vlong next)Int64.zero)
      (physical_world cgroup task_traced_stop next group)
| physical_continue : forall options group,
    physical_operation cgroup actor(physical_world cgroup task_traced_stop options group)
      (process_traced(Int.repr 7)(Int.repr 2)(Vlong Int64.zero)(Vlong Int64.zero)Int64.zero)
      (physical_world cgroup task_running options group).

Lemma physical_owns cgroup phase options group :
  OwnsUnreaped(physical_world cgroup phase options group)physical_parent physical_child.
Proof. unfold OwnsUnreaped,physical_world,physical_child;cbn;rewrite Int.eq_true;auto. Qed.

Lemma physical_owner_unique cgroup phase options group parent child :
  OwnsUnreaped(physical_world cgroup phase options group)parent child ->
  parent=physical_parent /\child=physical_child.
Proof.
  intros[PID[PARENT REST]];cbn in PID,PARENT.
  destruct(Int.eq(task_pid child)(Int.repr 2));[inversion PID;auto|discriminate].
Qed.



Lemma physical_stopped cgroup options group :
  OwnsStopped(physical_world cgroup task_traced_stop options group)physical_parent physical_child.
Proof. split;[apply physical_owns|];split;reflexivity. Qed.

Ltac physical_event_cases :=
  match goal with PASSIVE:physical_passive ?event=true|-_=>
    destruct event;try discriminate;
    repeat match goal with
    |H:physical_passive(process_entry ?event)=true|-_=>destruct event;try discriminate
    |H:physical_passive(process_entry(entry_library ?event))=true|-_=>destruct event;try discriminate
    |H:physical_passive(process_entry(entry_library(original_event ?event)))=true|-_=>destruct event;try discriminate
    end
  end.

Theorem physical_linux_contract cgroup : LinuxProcessContract(physical_operation cgroup).
Proof.
  constructor.
  - intros before after parent child event OWN NONREAP OP.
    inversion OP;subst;destruct(physical_owner_unique _ _ _ _ _ _ OWN)as[PARENT CHILD];
      subst parent child;apply physical_owns.
  - intros before after parent event FILE OP;inversion OP;subst;reflexivity.
  - intros before after parent child event OWN FRAME OP.
    inversion OP;subst;try reflexivity.
    destruct FRAME as[NONREAP OTHER];cbn[process_scope_frame_event process_machine_event]in OTHER.
    change((if Int.eq(IO.descriptor q)(IO.descriptor q)then Some 1%nat else None)=None)in OTHER.
    rewrite Int.eq_true in OTHER;discriminate.
  - intros before after parent child trace OWN OP.
    inversion OP;subst;try discriminate.
    + split;[exact OWN|];split;reflexivity.
  - intros before after parent child OWN OP.
    inversion OP;subst;try discriminate.
    + split;[exact OWN|];split;reflexivity.
  - intros before after parent child q reply OWN OP.
    inversion OP;subst;try discriminate.
    + destruct(physical_owner_unique _ _ _ _ _ _ OWN)as[PARENT CHILD];subst.
      split;[apply physical_owns|reflexivity].
  - intros before after parent child q reply OWN OTHER OP.
    inversion OP;subst;try discriminate.
    + change((if Int.eq(IO.descriptor q)(IO.descriptor q)then Some 1%nat else None)=None)in OTHER;
      rewrite Int.eq_true in OTHER;discriminate.
  - intros before after parent child status offset word OWN OP STOP SIGNAL.
    inversion OP;subst;try discriminate.
    + destruct(physical_owner_unique _ _ _ _ _ _ OWN)as[PARENT CHILD];subst;apply physical_stopped.
  - intros before after parent child status offset OWN OP.
    inversion OP;subst;try discriminate;exact OWN.
  - intros before after parent q bytes error group WRITING FILE OP.
    inversion OP;subst;try discriminate.
    + assumption.
  - intros before after parent child q bytes error group OWN WRITING FILE CANON OP.
    inversion OP;subst;try discriminate.
    + destruct(physical_owner_unique _ _ _ _ _ _ OWN)as[PARENT CHILD];subst.
      change((if Int.eq(IO.descriptor q)(IO.descriptor q)then Some 1%nat else None)=Some group)in FILE;
      rewrite Int.eq_true in FILE;inversion FILE;subst.
      split;[apply physical_owns|reflexivity].
  - intros before after parent child options OWN OP.
    inversion OP;subst;try discriminate.
    + destruct(physical_owner_unique _ _ _ _ _ _ OWN)as[PARENT CHILD];subst.
      split;[apply physical_stopped|];split;[apply physical_stopped|];split;reflexivity.
  - intros before after parent child OWN OP.
    inversion OP;subst;try discriminate.
    + destruct(physical_owner_unique _ _ _ _ _ _ OWN)as[PARENT CHILD];subst.
      split;[apply physical_stopped|]. split;[apply physical_owns|]. repeat split;reflexivity.
Qed.

Lemma physical_no_interference parent child world : ProcessInterference parent child world world.
Proof. constructor;intros;reflexivity||assumption. Qed.

Theorem physical_passive_trace cgroup parent child phase options group events :
  Forall(fun event=>physical_passive event=true)events ->
  process_world_steps(physical_operation cgroup)parent child
    (physical_world cgroup phase options group)events(physical_world cgroup phase options group).
Proof.
  intro EVENTS;induction EVENTS;[constructor|].
  econstructor;[apply physical_no_interference|constructor;exact H|exact IHEVENTS].
Qed.


Lemma physical_trace_append operation parent child before prefix middle suffix after :
  process_world_steps operation parent child before prefix middle ->
  process_world_steps operation parent child middle suffix after ->
  process_world_steps operation parent child before(prefix++suffix)after.
Proof.
  intro PREFIX;induction PREFIX as[world|first observed event next events last INTERFERENCE STEP RUN IH];
    intros SUFFIX;cbn;[exact SUFFIX|].
  econstructor;[exact INTERFERENCE|exact STEP|apply IH;exact SUFFIX].
Qed.

(* This trace has exactly the event shape of the maintained useful source
   execution: source/formatting work around the matching stop, whole PID write
   and checked options. It therefore supplies the physical half of that same
   source witness, rather than a separate independently chosen successful run. *)
Theorem physical_admission_trace cgroup status offset word q bytes error
    before_stop before_write before_options suffix :
  Forall(fun event=>physical_passive event=true)before_stop ->
  Forall(fun event=>physical_passive event=true)before_write ->
  Forall(fun event=>physical_passive event=true)before_options ->
  Forall(fun event=>physical_passive event=true)suffix ->
  admission_is_stopped word=true ->admission_is_sigstop word=true ->
  IO.operation q=writing ->IO.descriptor q=cgroup ->
  Z.of_nat(length bytes)=requested q ->canonical_pid bytes physical_child ->
  process_world_steps(physical_operation cgroup)physical_parent physical_child
    (physical_world cgroup task_running Int64.zero None)
    (before_stop++process_waited(Int.repr 2)status offset Int.zero(wait_status(Int.repr 2)word)::
      (before_write++process_machine_event(io_step q(transfer bytes error))::
        (before_options++process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)
          (Vlong(Int64.repr 1048592))Int64.zero::suffix)))
    (physical_world cgroup task_traced_stop(Int64.repr 1048592)(Some 1%nat)).
Proof.
  intros STOP_PREFIX WRITE_PREFIX OPTIONS_PREFIX SUFFIX STOP SIGNAL WRITING FD LENGTH CANON.
  eapply physical_trace_append;[apply physical_passive_trace;exact STOP_PREFIX|].
  econstructor;[apply physical_no_interference|apply physical_wait_stop;assumption|].
  eapply physical_trace_append;[apply physical_passive_trace;exact WRITE_PREFIX|].
  econstructor;[apply physical_no_interference|eapply physical_place;try eassumption|].
  eapply physical_trace_append;[apply physical_passive_trace;exact OPTIONS_PREFIX|].
  econstructor;[apply physical_no_interference|apply physical_options|].
  apply physical_passive_trace;exact SUFFIX.
Qed.

Lemma physical_source_repeat count:
  Forall(fun event=>physical_passive event=true)(repeat process_source_event count).
Proof. induction count;cbn;constructor;auto. Qed.

Definition physical_admission_events cell locals cgroup status first second:=
  repeat process_source_event 5++
    process_waited(Int.repr 2)status Ptrofs.zero Int.zero(wait_status(Int.repr 2)(Int.repr 4991))::
    (repeat process_source_event 29++
      process_entry(entry_formatted(admission_text locals)Ptrofs.zero(Int64.repr 2)Int.one)::
      (repeat process_source_event first++
        placement_lift(io_step(admission_write_request cell locals cgroup Int.one)(transfer[Byte.repr 50]None))::
        (repeat process_source_event second++
          process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)
            (Vlong(Int64.repr 1048592))Int64.zero::repeat process_source_event 5))).

(* The source and physical histories below are identical, including formatter
   and memory-control steps, not merely their three successful effect labels. *)
Theorem actual_useful_admission_has_physical_execution cell before cgroup status error:
  initialized_errno cell before error ->Mem.valid_access before Mint32 status 0 Writable ->
  status<>tls_block cell ->
  exists locals first second after,
    process_steps admission_ge cell
      (live(Callstate(Internal EntrySource.f_admit_child)
        [Vint(Int.repr 2);Vint cgroup;Vptr status Ptrofs.zero]Kstop before))
      (physical_admission_events cell locals cgroup status first second)
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    process_world_steps(physical_operation cgroup)physical_parent physical_child
      (physical_world cgroup task_running Int64.zero None)
      (physical_admission_events cell locals cgroup status first second)
      (physical_world cgroup task_traced_stop(Int64.repr 1048592)(Some 1%nat)).
Proof.
  intros ERRNO ACCESS SEPARATE.
  destruct(admission_useful_source_execution cell before cgroup status error ERRNO ACCESS SEPARATE)
    as[locals[first[second[after SOURCE]]]].
  exists locals,first,second,after;split;[exact SOURCE|].
  unfold physical_admission_events.
  change(process_world_steps(physical_operation cgroup)physical_parent physical_child
    (physical_world cgroup task_running Int64.zero None)
    (repeat process_source_event 5++
      process_waited(Int.repr 2)status Ptrofs.zero Int.zero(wait_status(Int.repr 2)(Int.repr 4991))::
      ((repeat process_source_event 29++
        process_entry(entry_formatted(admission_text locals)Ptrofs.zero(Int64.repr 2)Int.one)::
          repeat process_source_event first)++
        process_machine_event(io_step(admission_write_request cell locals cgroup Int.one)(transfer[Byte.repr 50]None))::
        (repeat process_source_event second++
          process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)
            (Vlong(Int64.repr 1048592))Int64.zero::repeat process_source_event 5)))
    (physical_world cgroup task_traced_stop(Int64.repr 1048592)(Some 1%nat))).
  eapply physical_admission_trace.
  - apply physical_source_repeat.
  - apply Forall_app;split;[apply physical_source_repeat|].
    constructor;[reflexivity|apply physical_source_repeat].
  - apply physical_source_repeat.
  - apply physical_source_repeat.
  - vm_compute;reflexivity.
  - vm_compute;reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - split.
    + constructor;[change(48<=50<=57);lia|constructor].
    + split.
      * exists(Byte.repr 50),[];split;[reflexivity|vm_compute;discriminate].
      * vm_compute;reflexivity.
Qed.

Theorem actual_source_and_physical_admission_useful cgroup:
  exists initial cell before status locals first second after,
    Genv.init_mem EntrySource.prog=Some initial /\
    process_steps admission_ge cell
      (live(Callstate(Internal EntrySource.f_admit_child)
        [Vint(Int.repr 2);Vint cgroup;Vptr status Ptrofs.zero]Kstop before))
      (physical_admission_events cell locals cgroup status first second)
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    process_world_steps(physical_operation cgroup)physical_parent physical_child
      (physical_world cgroup task_running Int64.zero None)
      (physical_admission_events cell locals cgroup status first second)
      (physical_world cgroup task_traced_stop(Int64.repr 1048592)(Some 1%nat)) /\
    admission_kernel_snapshots(physical_operation cgroup)cell physical_parent physical_child
      (physical_world cgroup task_running Int64.zero None)
      (physical_admission_events cell locals cgroup status first second)
      (physical_world cgroup task_traced_stop(Int64.repr 1048592)(Some 1%nat))cgroup 1%nat.
Proof.
  destruct admission_actual_useful_input as[initial[cell[before[status[INITIAL[ERRNO[ACCESS SEPARATE]]]]]]].
  destruct(actual_useful_admission_has_physical_execution cell before cgroup status(Int.repr 5)
    ERRNO ACCESS SEPARATE)as[locals[first[second[after[SOURCE PHYSICAL]]]]].
  exists initial,cell,before,status,locals,first,second,after.
  split;[exact INITIAL|]. split;[exact SOURCE|]. split;[exact PHYSICAL|].
  eapply actual_admission_establishes_scope with(before_memory:=before)(after_memory:=after)
    (status:=status)(offset:=Ptrofs.zero).
  - exact(physical_linux_contract cgroup).
  - change(1<=2);lia.
  - exact SEPARATE.
  - exists(Int.repr 5);exact ERRNO.
  - apply physical_owns.
  - change((if Int.eq cgroup cgroup then Some 1%nat else None)=Some 1%nat).
    rewrite Int.eq_true;reflexivity.
  - exact SOURCE.
  - exact PHYSICAL.
Qed.
