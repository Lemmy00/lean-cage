(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Consume release evidence from the actual wider namespace callback run. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import IO Machine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessGlobalCalls ProcessCaller ProcessReleaseSafety.
From EntryNamespace Require Import NamespaceMachine NamespaceClosure NamespaceAdmissionProjection NamespaceSocket.
Import ListNotations.
Open Scope Z_scope.

Definition release_call_profile:=[_release_child;_entry_ptrace4;_write].
Theorem release_call_profile_checked:closure_profile release_call_profile=true.
Proof. vm_compute;reflexivity. Qed.
Theorem release_call_profile_no_namespace:closure_excludes release_call_profile namespace_primitive_names=true.
Proof. vm_compute;reflexivity. Qed.

Lemma release_call_profile_start arguments memory:
  closure_state release_call_profile(Callstate(Internal f_release_child)arguments Kstop memory).
Proof.
  split.
  - split;[vm_compute;reflexivity|exact I].
  - split.
    + exists _release_child;split;[left;reflexivity|vm_compute;reflexivity].
    + exact I.
Qed.

Theorem actual_namespace_release_projects cell arguments memory events target:
  namespace_steps caller_ge cell(live(Callstate(Internal f_release_child)arguments Kstop memory))events target ->
  exists actual,events=map namespace_process actual /\
    process_steps caller_ge cell(live(Callstate(Internal f_release_child)arguments Kstop memory))actual target.
Proof.
  intro RUN;eapply closure_namespace_runs_are_process_runs;
    [exact release_call_profile_checked|exact release_call_profile_no_namespace|
     apply release_call_profile_start|exact RUN].
Qed.

Lemma mapped_source_occurrence(A B:Type)(project:A->B)actual prefix event suffix:
  map project actual=prefix++event::suffix ->
  exists before selected after,actual=before++selected::after /\
    prefix=map project before /\event=project selected /\suffix=map project after.
Proof.
  revert actual;induction prefix as[|first rest IH];intros actual SAME;
    destruct actual as[|source remaining];cbn in SAME;try discriminate.
  - injection SAME as EVENT EVENTS;exists[],source,remaining;cbn;repeat split;congruence.
  - injection SAME as FIRST REST.
    destruct(IH remaining REST)as[before[selected[after[ACTUAL[PREFIX[EVENT SUFFIX]]]]]].
    exists(source::before),selected,after;cbn;rewrite ACTUAL,PREFIX;repeat split;congruence.
Qed.

Theorem actual_namespace_release_socket_checked_from_live_tls cell before child peer events target prefix event suffix io:
  Mem.valid_block before(tls_block cell) ->
  namespace_steps caller_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events target ->
  events=prefix++event::suffix ->namespace_socket_io event=Some io ->
  In(namespace_process(release_resume_event child))prefix /\
    operation(source_socket_request io)=writing /\descriptor(source_socket_request io)=peer /\
    requested(source_socket_request io)=1 /\source_socket_bytes io=[Byte.repr 165].
Proof.
  intros READY RUN EVENTS SOCKET.
  destruct(actual_namespace_release_projects _ _ _ _ _ RUN)as[actual[PROJECT REAL]].
  rewrite PROJECT in EVENTS.
  destruct(mapped_source_occurrence _ _ _ _ _ _ _ EVENTS)
    as[before_events[selected[after_events[ACTUAL[PREFIX[EVENT SUFFIX]]]]]].
  subst prefix event suffix;cbn[namespace_socket_io]in SOCKET.
  change(process_steps admission_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))actual target)in REAL.
  destruct(actual_release_socket_has_checked_resume_from_live_tls _ _ _ _ _ _ _ _ _ _ READY REAL ACTUAL SOCKET)
    as[RESUMED BYTE].
  split;[apply in_map;exact RESUMED|exact BYTE].
Qed.

Theorem actual_namespace_release_socket_checked cell before child peer events target prefix event suffix io:
  entry_errno_ready cell before ->
  namespace_steps caller_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events target ->
  events=prefix++event::suffix ->namespace_socket_io event=Some io ->
  In(namespace_process(release_resume_event child))prefix /\
    operation(source_socket_request io)=writing /\descriptor(source_socket_request io)=peer /\
    requested(source_socket_request io)=1 /\source_socket_bytes io=[Byte.repr 165].
Proof.
  intros READY RUN EVENTS SOCKET.
  destruct(actual_namespace_release_projects _ _ _ _ _ RUN)as[actual[PROJECT REAL]].
  rewrite PROJECT in EVENTS.
  destruct(mapped_source_occurrence _ _ _ _ _ _ _ EVENTS)
    as[before_events[selected[after_events[ACTUAL[PREFIX[EVENT SUFFIX]]]]]].
  subst prefix event suffix;cbn[namespace_socket_io]in SOCKET.
  change(process_steps admission_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))actual target)in REAL.
  destruct(actual_release_socket_has_checked_resume _ _ _ _ _ _ _ _ _ _ READY REAL ACTUAL SOCKET)
    as[RESUMED BYTE].
  split;[apply in_map;exact RESUMED|exact BYTE].
Qed.

Theorem actual_namespace_release_socket_resumed cell before child peer events target prefix event suffix io:
  namespace_steps caller_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events target ->
  events=prefix++event::suffix ->namespace_socket_io event=Some io ->
  In(namespace_process(release_resume_event child))prefix.
Proof.
  intros RUN EVENTS SOCKET.
  destruct(actual_namespace_release_projects _ _ _ _ _ RUN)as[actual[PROJECT REAL]].
  rewrite PROJECT in EVENTS.
  destruct(mapped_source_occurrence _ _ _ _ _ _ _ EVENTS)
    as[before_events[selected[after_events[ACTUAL[PREFIX[EVENT SUFFIX]]]]]].
  subst prefix event suffix;cbn[namespace_socket_io]in SOCKET.
  change(process_steps admission_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))actual target)in REAL.
  apply in_map;eapply release_transport_requires_checked_resume;
    [exact REAL|exact ACTUAL|eapply process_socket_io_transports;exact SOCKET].
Qed.
