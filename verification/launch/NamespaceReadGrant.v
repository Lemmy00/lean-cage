(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Exact read provenance and per-operation ownership select the real parent source send. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessSourceRecording ProcessSourceTables.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceCapabilities NamespaceChannel NamespacePhysical
  NamespaceGrant NamespaceByteOrigin NamespaceWriteOrigin NamespaceChildOrigin NamespaceDescriptorFrame.
Import ListNotations.
Local Close Scope lean_scope.

Theorem actual_bound_read_parent_source_send operation groups runs cursor worlds ticks final final_worlds owner child
    child_program child_run channel failure queue_after start read_offset read_tick read_fd flag:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  SourceProgramOwner runs child child_program ->nth_error runs child_program=Some child_run ->
  (forall offset tick,nth_error ticks offset=Some tick ->SourceIO runs tick) ->
  (forall offset tick,nth_error ticks offset=Some tick ->
    LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick) ->
  (forall offset tick actor,nth_error ticks offset=Some tick ->
    unrelated(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))actor ->channel_absent(physical_tick_table tick actor)channel) ->
  Forall(fun event=>namespace_after_fork_event event=true)(source_events child_run) ->
  (forall event io,In event(source_events child_run) ->NamespaceSocket.namespace_socket_io event=Some io ->
    IO.operation(NamespaceSocket.source_socket_request io)=IO.writing ->
    IO.descriptor(NamespaceSocket.source_socket_request io)=failure) ->
  excludes_parent_at(namespace_table(worlds child_program))channel failure ->
  physical_queue_execution channel channel_empty ticks queue_after ->nth_error ticks read_offset=Some read_tick ->
  Lean.eq(ProcessImport.socket read_tick)(LeanCage_Entry_CallerPhysical_SocketObservation_read child
    (NamespaceHandles.native_descriptor_number read_fd)(Nat_of_nat 1)physical_grant_bytes) ->
  (0<=Int.signed read_fd)%Z ->
  LeanCage_Entry_CallerPhysical_TickBinding read_tick(LeanCage_Entry_CallerPhysical_taskKey child)
    (NamespaceHandles.native_descriptor_number read_fd)
    (NamespaceHandles.native_descriptor_object(release_endpoint channel child_endpoint))(physical_flag flag) ->
  exists send_offset sent_tick source_fd bytes lost,
    nth_error ticks send_offset=Some sent_tick /\(send_offset<read_offset)%nat /\
    physical_tick_projection channel sent_tick=(physical_tick_table sent_tick,
      channel_sent(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))source_fd bytes lost) /\
    (exists binding,physical_tick_table sent_tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner))source_fd=Some binding /\
      descriptor_object binding=release_endpoint channel parent_endpoint) /\
    (exists reference,LeanCage_Entry_CallerPhysical_Tick_source sent_tick=
      ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference reference) /\
    In(Byte.repr 165)bytes /\checked_grant_order(start+send_offset)(start+read_offset).
Proof.
  intros TABLES CHILD_OWNER CHILD_PROGRAM SOURCE ORIGINS FOREIGN PROFILE WRITES FAILURE QUEUE SELECTED SOCKET NONNEGATIVE BINDING.
  assert(SOCKET':ProcessImport.socket read_tick=LeanCage_Entry_CallerPhysical_SocketObservation_read child
    (NamespaceHandles.native_descriptor_number read_fd)(Nat_of_nat 1)physical_grant_bytes)by(destruct SOCKET;reflexivity).
  pose proof(strict_tick_binding_is_actual _ _ _ _ _ NONNEGATIVE BINDING)as PRESENT.
  destruct(actual_read_has_exact_prior_send channel ticks queue_after read_offset read_tick child read_fd 1 physical_grant_bytes
    {|descriptor_object:=release_endpoint channel child_endpoint;descriptor_cloexec:=flag|}
    QUEUE SELECTED SOCKET' (Logic.eq_refl _) NONNEGATIVE PRESENT (Logic.eq_refl _) ltac:(left;reflexivity))
    as[send_offset[sent_tick[sender[source_fd[bytes[lost[binding[SEND[BEFORE[PROJECT[FD[OBJECT BYTE]]]]]]]]]]]].
  assert(HOLDER:sender=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner)\/
      sender=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)).
  { destruct(Nat.eq_dec sender(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner)))as[PARENT|OTHER];[auto|].
    destruct(Nat.eq_dec sender(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)))as[CHILD|FOREIGN_CHILD];[auto|].
    exfalso;exact(FOREIGN _ _ _ SEND(conj OTHER FOREIGN_CHILD)_ _ parent_endpoint FD OBJECT). }
  pose proof(actual_holder_send_has_source _ _ _ _ _ _ _ _(ORIGINS _ _ SEND)HOLDER PROJECT)as REFERENCE.
  assert(PARENT:sender=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner)).
  { destruct HOLDER as[PARENT|CHILD];[exact PARENT|].
    exfalso;rewrite CHILD in PROJECT,FD.
    eapply actual_child_endpoint_send_impossible;[exact TABLES|exact CHILD_OWNER|exact CHILD_PROGRAM|exact SEND|
      exact(SOURCE _ _ SEND)|exact REFERENCE|exact PROJECT|exact FD|exact OBJECT|exact PROFILE|exact WRITES|exact FAILURE]. }
  subst sender.
  exists send_offset,sent_tick,source_fd,bytes,lost.
  split;[exact SEND|]. split;[exact BEFORE|]. split;[exact PROJECT|]. split;[exists binding;auto|].
  split;[exact REFERENCE|]. split;[exact BYTE|constructor;apply physical_order_is_ordinary;lia].
Qed.
