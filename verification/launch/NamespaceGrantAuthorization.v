(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: A private write must cross the actual checked parent release call. *)
From Stdlib Require Import ZArith List Lia Bool String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine CallContexts StoreSteps.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller ProcessDescriptor
  ProcessAdmissionDescriptor.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceContexts
  NamespaceAdmission NamespaceParentSafety NamespaceSocket NamespaceClosure NamespaceAdmissionProjection
  NamespaceTailDescriptor.
Import ListNotations.
Open Scope Z_scope.

Definition private_namespace_write peer event:=exists io,namespace_socket_io event=Some io /\
  operation(source_socket_request io)=writing /\descriptor(source_socket_request io)=peer.

Lemma descriptor_observed_socket fd event io:
  descriptor_namespace_event fd event ->namespace_socket_io event=Some io ->
  operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=fd.
Proof.
  intros DESCRIPTOR SOCKET WRITING.
  unfold descriptor_namespace_event,descriptor_process_event,descriptor_entry_event,
    descriptor_library_event,descriptor_io_event in DESCRIPTOR.
  unfold namespace_socket_io,process_socket_io in SOCKET.
  repeat match goal with
  |e:namespace_event|-_=>destruct e;cbn in SOCKET,DESCRIPTOR;try discriminate
  |e:process_event|-_=>destruct e;cbn in SOCKET,DESCRIPTOR;try discriminate
  |e:entry_handoff_event|-_=>destruct e;cbn in SOCKET,DESCRIPTOR;try discriminate
  |e:library_event|-_=>destruct e;cbn in SOCKET,DESCRIPTOR;try discriminate
  |e:Machine.event|-_=>destruct e;cbn in SOCKET,DESCRIPTOR;try discriminate
  |r:reply|-_=>destruct r;cbn in SOCKET,DESCRIPTOR;try discriminate
  end;inversion SOCKET;subst;cbn in *;apply DESCRIPTOR;exact WRITING.
Qed.

Lemma descriptor_excludes_private fd peer event:
  fd<>peer ->descriptor_namespace_event fd event ->~private_namespace_write peer event.
Proof.
  intros OTHER DESCRIPTOR[io[SOCKET[WRITING PEER]]].
  pose proof(descriptor_observed_socket _ _ _ DESCRIPTOR SOCKET WRITING);congruence.
Qed.

Definition callback_excludes_private ge cell definition arguments memory peer:=
  forall events target,namespace_steps ge cell(live(Callstate definition arguments Kstop memory))events target ->
    Forall(fun event=>~private_namespace_write peer event)events.

Theorem callback_returns_before_private_write ge cell definition arguments continuation memory peer
    events called values write_cont write_memory event after:
  is_call_cont continuation ->callback_excludes_private ge cell definition arguments memory peer ->
  namespace_steps ge cell(live(Callstate definition arguments continuation memory))events
    (live(Callstate called values write_cont write_memory)) ->
  namespace_step ge cell(live(Callstate called values write_cont write_memory))event after ->
  private_namespace_write peer event ->
  exists prefix rest returned result,events=prefix++rest /\
    namespace_steps ge cell(live(Callstate definition arguments Kstop memory))prefix
      (live(Returnstate returned Kstop result)) /\
    namespace_steps ge cell(live(Returnstate returned continuation result))rest
      (live(Callstate called values write_cont write_memory)).
Proof.
  intros CALL EXCLUDED RUN WRITE PRIVATE.
  destruct(namespace_caller_run_decomposition ge cell continuation(Callstate definition arguments Kstop memory)
    events(live(Callstate called values write_cont write_memory))CALL RUN)
    as[[local[LOCAL SAME]]|[prefix[rest[returned[result[EVENTS[LOCAL REMAINING]]]]]]].
  - destruct local as[current|dead_memory];[|discriminate].
    change(live(Callstate called values write_cont write_memory)=live(plug_state current continuation))in SAME.
    assert(NOTRETURN:~local_return current).
    { intros[value[result RETURN]];subst current;discriminate SAME. }
    assert(WRITE':namespace_step ge cell(live(plug_state current continuation))event after).
    { rewrite <-SAME;exact WRITE. }
    destruct(unplug_namespace_step ge cell current event after continuation CALL NOTRETURN WRITE')
      as[next[STEP TARGET]].
    assert(ACTUAL:namespace_steps ge cell(live(Callstate definition arguments Kstop memory))
      (events++[event])next).
    { eapply namespace_steps_append;[exact LOCAL|econstructor;[exact STEP|constructor]]. }
    pose proof(EXCLUDED _ _ ACTUAL)as NONE;rewrite Forall_forall in NONE.
    exfalso;apply(NONE event);[apply in_or_app;right;left;reflexivity|exact PRIVATE].
  - exists prefix,rest,returned,result;auto.
Qed.

Theorem admission_excludes_private cell child cgroup status memory peer:
  cgroup<>peer ->callback_excludes_private caller_ge cell(Internal f_admit_child)
    [Vint child;Vint cgroup;status]memory peer.
Proof.
  intros OTHER events target RUN.
  pose proof(actual_admit_namespace_write_descriptors _ _ _ _ _ _ _ RUN)as FD.
  eapply Forall_impl;[|exact FD];intros event CHECK;eapply descriptor_excludes_private;eassumption.
Qed.

Theorem sender_excludes_private cell report sequence value memory peer:
  report<>peer ->callback_excludes_private caller_ge cell(Internal f_send_frame)
    [Vint report;Vlong sequence;value]memory peer.
Proof.
  intros OTHER events target RUN.
  pose proof(actual_sender_namespace_write_descriptors _ _ _ _ _ _ _ RUN)as FD.
  eapply Forall_impl;[|exact FD];intros event CHECK;eapply descriptor_excludes_private;eassumption.
Qed.


Lemma namespace_socket_step_call ge cell before event after io:
  namespace_step ge cell before event after ->namespace_socket_io event=Some io ->
  exists k memory,before=live(Callstate
    (External(io_function(operation(source_socket_request io)))[tint;tptr tvoid;tulong]tlong cc_default)
    (request_args(source_socket_request io))k memory).
Proof.
  intros STEP SOCKET;unfold namespace_socket_io,process_socket_io in SOCKET.
  repeat match goal with
  |e:namespace_event|-_=>destruct e;cbn in SOCKET;try discriminate
  |e:process_event|-_=>destruct e;cbn in SOCKET;try discriminate
  |e:entry_handoff_event|-_=>destruct e;cbn in SOCKET;try discriminate
  |e:library_event|-_=>destruct e;cbn in SOCKET;try discriminate
  |e:Machine.event|-_=>destruct e;cbn in SOCKET;try discriminate
  |r:reply|-_=>destruct r;cbn in SOCKET;try discriminate
  end;inversion SOCKET;subst;cbn.
  all:inversion STEP;subst;
    match goal with P:process_step _ _ _ _ _|-_=>inversion P;subst end;
    match goal with E:entry_handoff_step _ _ _ _ _|-_=>inversion E;subst end;
    match goal with L:library_step _ _ _ _ _|-_=>inversion L;subst end;
    match goal with M:Machine.step _ _ _ _ _|-_=>inversion M;subst end;
    do 2 eexists;reflexivity.
Qed.

Lemma closed_namespace_step_no_write ids cell before event after peer:
  closure_excludes ids ["write"]%string=true ->closure_machine ids before ->
  namespace_step caller_ge cell before event after ->~private_namespace_write peer event.
Proof.
  intros EXCLUDED GOOD STEP[io[SOCKET[WRITING FD]]].
  destruct(namespace_socket_step_call _ _ _ _ _ _ STEP SOCKET)as[k[memory SAME]];subst before.
  destruct GOOD as[GLOBAL[FUNCTION CONT]].
  pose proof(closure_excluded_function _ _ _ EXCLUDED FUNCTION)as OUTSIDE.
  rewrite WRITING in OUTSIDE;change(true=false)in OUTSIDE;discriminate.
Qed.

Theorem closed_callback_excludes_private ids cell definition arguments memory peer:
  closure_profile ids=true ->closure_excludes ids ["write"]%string=true ->
  closure_state ids(Callstate definition arguments Kstop memory) ->
  callback_excludes_private caller_ge cell definition arguments memory peer.
Proof.
  intros PROFILE EXCLUDED GOOD events target RUN.
  change(closure_machine ids(live(Callstate definition arguments Kstop memory)))in GOOD;revert GOOD.
  induction RUN as[initial|initial event middle rest last STEP RUN IH];intros GOOD;[constructor|].
  constructor;[eapply closed_namespace_step_no_write;eassumption|].
  apply IH;eapply closure_namespace_step;eassumption.
Qed.

Definition result_call_profile:=[_result_of;_memcpy].
Theorem result_call_profile_checked:closure_profile result_call_profile=true.
Proof. vm_compute;reflexivity. Qed.

Theorem close_excludes_private cell cgroup memory peer:
  callback_excludes_private caller_ge cell close_definition[Vint cgroup]memory peer.
Proof.
  eapply closed_callback_excludes_private with(ids:=[_close]);
    [vm_compute;reflexivity|vm_compute;reflexivity|].
  split;[exact I|split;[exists _close;split;[left;reflexivity|vm_compute;reflexivity]|exact I]].
Qed.

Theorem result_excludes_private cell arguments memory peer:
  callback_excludes_private caller_ge cell(Internal f_result_of)arguments memory peer.
Proof.
  eapply closed_callback_excludes_private with(ids:=result_call_profile);
    [exact result_call_profile_checked|vm_compute;reflexivity|].
  eapply closure_start_named_call with(id:=_result_of);
    [left;reflexivity|vm_compute;reflexivity|vm_compute;reflexivity].
Qed.

Theorem clock_excludes_private cell arguments memory peer:
  callback_excludes_private caller_ge cell(Internal f_now_ms)arguments memory peer.
Proof.
  eapply closed_callback_excludes_private with(ids:=clock_call_profile);
    [exact clock_call_profile_checked|vm_compute;reflexivity|].
  eapply closure_start_named_call with(id:=_now_ms);
    [left;reflexivity|vm_compute;reflexivity|vm_compute;reflexivity].
Qed.


Theorem namespace_grant_plug_steps ge cell before events after suffix:
  is_call_cont suffix ->namespace_steps ge cell before events after ->
  namespace_steps ge cell(plug_machine before suffix)events(plug_machine after suffix).
Proof.
  intros CALL RUN;induction RUN as[initial|initial event middle rest last STEP RUN IH];[constructor|].
  econstructor;[exact(plug_namespace_step ge cell initial event middle suffix CALL STEP)|exact IH].
Qed.

Lemma namespace_grant_store_step ge cell before after:
  store_edge ge before after ->namespace_step ge cell(live before)namespace_source_event(live after).
Proof.
  intros[INTERNAL[STEP UNIQUE]].
  apply namespace_process_step,process_entry_step,entry_library_step,LibraryMachine.original_step,internal;assumption.
Qed.
