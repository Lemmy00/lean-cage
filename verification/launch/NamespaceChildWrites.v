(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: The same fork child's complete pre-worker source writes only its failure socket. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryProcess Require Import ProcessMachine ProcessDescriptor.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceMemory NamespaceChildResult
  NamespaceForkPrefix NamespaceFork NamespaceKernel NamespaceWorldTrace NamespaceChildImage NamespaceGuestDescriptor
  NamespaceSocket NamespaceQueue NamespaceTraceRegion NamespaceLaunch NamespaceGuestFlags.
Import ListNotations.

Lemma namespace_unselected_not_partial_has_no_socket event:
  namespace_fd_event event=false ->namespace_partial_io event=false ->namespace_socket_io event=None.
Proof.
  unfold namespace_fd_event,namespace_partial_io,namespace_socket_io,process_socket_io.
  repeat match goal with
  |event:namespace_event|-_=>destruct event;cbn;try discriminate;try reflexivity
  |event:process_event|-_=>destruct event;cbn;try discriminate;try reflexivity
  |event:entry_handoff_event|-_=>destruct event;cbn;try discriminate;try reflexivity
  |event:library_event|-_=>destruct event;cbn;try discriminate;try reflexivity
  |event:Machine.event|-_=>destruct event;cbn;try discriminate;try reflexivity
  |result:reply|-_=>destruct result;cbn;try discriminate;try reflexivity
  end.
Qed.
Lemma namespace_empty_fd_events events:
  namespace_fd_events events=[] ->Forall(fun event=>namespace_fd_event event=false)events.
Proof.
  unfold namespace_fd_events;induction events as[|event rest IH];cbn;[constructor|].
  destruct(namespace_fd_event event)eqn:SELECTED;[discriminate|].
  intro EMPTY;constructor;[exact SELECTED|apply IH;exact EMPTY].
Qed.
Theorem namespace_live_empty_fd_no_socket ge cell before events final:
  namespace_steps ge cell before events(live final) ->namespace_fd_events events=[] ->
  Forall(fun event=>namespace_socket_io event=None)events.
Proof.
  intros RUN EMPTY;pose proof(namespace_live_prefix_has_no_partial_io _ _ _ _ _ RUN)as PARTIAL.
  pose proof(namespace_empty_fd_events _ EMPTY)as NONE.
  rewrite Forall_forall in *;intros event MEMBER;eapply namespace_unselected_not_partial_has_no_socket;
    [apply NONE|apply PARTIAL];exact MEMBER.
Qed.

Lemma descriptor_namespace_event_socket fd event:
  descriptor_namespace_event fd event ->forall io,namespace_socket_io event=Some io ->
  operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=fd.
Proof.
  unfold descriptor_namespace_event,descriptor_process_event,descriptor_entry_event,descriptor_library_event,
    descriptor_io_event,namespace_socket_io,process_socket_io.
  repeat match goal with
  |event:namespace_event|-_=>destruct event;cbn;try discriminate
  |event:process_event|-_=>destruct event;cbn;try discriminate
  |event:entry_handoff_event|-_=>destruct event;cbn;try discriminate
  |event:library_event|-_=>destruct event;cbn;try discriminate
  |event:Machine.event|-_=>destruct event;cbn;try discriminate
  |result:reply|-_=>destruct result;cbn;try discriminate
  end;intros GOOD io SAME WRITING;inversion SAME;subst io;apply GOOD;exact WRITING.
Qed.

Theorem actual_child_branch_write_descriptors scope first second failure reply le before world snapshot parent child
    events target path arguments environment:
  scope_history scope=[] ->
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  fork_matches world snapshot ->NativeForkCopy(scope_cell scope)before parent child ->
  namespace_steps namespace_ge(scope_cell scope)
    (live(Returnstate(Vint Int.zero)(child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child))
    events target ->In(namespace_guest_event(entry_image path arguments environment))events ->
  forall event io,In event events ->namespace_socket_io event=Some io ->
    operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=failure.
Proof.
  intros HISTORY FRONTIER MATCH COPY RUN IMAGE.
  destruct(actual_child_branch_image_reaches_guest scope first second failure reply le before world snapshot parent child events target path arguments environment
    HISTORY FRONTIER MATCH COPY RUN IMAGE)
    as[prefix[rest[guest_le[memory[EVENTS[EMPTY[NOIMAGES[PRE[BORROWED[NONNEGATIVE[GUEST LATER]]]]]]]]]]].
  pose proof(namespace_live_empty_fd_no_socket _ _ _ _ _ PRE EMPTY)as QUIET.
  rewrite namespace_launch_environment in GUEST.
  assert(CALL:is_call_cont(child_guest_cont(storage_pair(scope_storage scope))guest_le(scope_continuation scope)))by exact I.
  pose proof(actual_namespace_guest_caller_write_descriptors(scope_cell scope)(scope_borrowed scope)memory
    (scope_input scope)(scope_output scope)(scope_errors scope)failure
    (child_guest_cont(storage_pair(scope_storage scope))guest_le(scope_continuation scope))rest target BORROWED CALL GUEST)as WRITES.
  intros event io MEMBER SOCKET WRITING;rewrite EVENTS in MEMBER;apply in_app_iff in MEMBER as[EARLY|LATE].
  - rewrite Forall_forall in QUIET;specialize(QUIET _ EARLY);congruence.
  - eapply descriptor_namespace_event_socket;[rewrite Forall_forall in WRITES;apply WRITES;exact LATE|exact SOCKET|exact WRITING].
Qed.

From EntryNamespace Require Import NamespaceDescriptorFrame NamespaceGuest.
Lemma namespace_unselected_is_after_fork event:
  namespace_fd_event event=false ->namespace_after_fork_event event=true.
Proof. destruct event;cbn;try discriminate;reflexivity. Qed.

Theorem actual_child_image_source_has_no_capability_export scope first second failure reply le before world snapshot parent child
    events target path arguments environment:
  scope_history scope=[] ->
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  fork_matches world snapshot ->NativeForkCopy(scope_cell scope)before parent child ->
  namespace_steps namespace_ge(scope_cell scope)
    (live(Returnstate(Vint Int.zero)(child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child))
    events target ->In(namespace_guest_event(entry_image path arguments environment))events ->
  Forall(fun event=>namespace_after_fork_event event=true)events.
Proof.
  intros HISTORY FRONTIER MATCH COPY RUN IMAGE.
  destruct(actual_child_branch_image_reaches_guest scope first second failure reply le before world snapshot parent child events target path arguments environment
    HISTORY FRONTIER MATCH COPY RUN IMAGE)
    as[prefix[rest[guest_le[memory[EVENTS[EMPTY[NOIMAGES[PRE[BORROWED[NONNEGATIVE[GUEST LATER]]]]]]]]]]].
  rewrite EVENTS;apply Forall_app;split.
  - pose proof(namespace_empty_fd_events _ EMPTY)as NONE.
    eapply Forall_impl;[|exact NONE];intros event UNSELECTED;apply namespace_unselected_is_after_fork;exact UNSELECTED.
  - rewrite namespace_launch_environment in GUEST.
    destruct(actual_namespace_guest_projects _ _ _ _ _ _ _ _ _ _ BORROWED GUEST)as[actual[REST REAL]].
    rewrite REST;apply Forall_forall;intros event MEMBER;apply in_map_iff in MEMBER as[original[SAME MEMBER]].
    subst event;reflexivity.
Qed.
