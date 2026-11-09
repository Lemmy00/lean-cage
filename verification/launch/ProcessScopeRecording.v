(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.image: Actual descriptor observations rule out later parent cgroup placement. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessScope ProcessJournal ProcessCallerConnection.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceWorldTrace
  NamespacePhysical NamespaceSocket.
Import ListNotations.
Local Close Scope lean_scope.

(* The filesystem/kernel binding classifies all cgroup-placement command
   objects and the group each one commands. Socket objects are separate. *)
Definition CgroupObjects := nat->option nat.
Definition cgroup_unique_aliases (groups:CgroupObjects) table descriptor :=
  forall object group,groups object=Some group ->
    unique_object_alias table(ordinary_object object)descriptor.

Definition PlacementObservation (groups:CgroupObjects) tick group :=
  exists actor fd binding object bytes lost,
    ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor
      (Nat_of_nat(Z.to_nat(Int.unsigned fd)))bytes lost /\
    physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd=Some binding /\
    descriptor_object binding=ordinary_object object /\groups object=Some(nat_of_Nat group).

(* This is one genuine cgroup-changing write's classification at its actual
   linearization point. It imposes no ordering or suffix-safety property. *)
Definition PlacementRecording groups tick := forall group,
  LeanCage_Entry_CallerPhysical_Tick_action tick=LeanCage_Entry_CallerPhysical_Action_placement group ->
  PlacementObservation groups tick group.

Theorem actual_close_forbids_recorded_parent_placement groups before descriptor reply closed
    events at_write tick actor :
  cgroup_unique_aliases groups(namespace_table before)descriptor ->
  namespace_kernel_event before
    (namespace_process(process_entry(entry_library(close_returned descriptor reply))))closed ->
  close_value reply=Int.zero ->namespace_kernel_steps closed events at_write ->
  (forall fd,physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd=
    namespace_table at_write fd) ->
  PlacementRecording groups tick ->
  (forall writer fd bytes lost,
    ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote writer fd bytes lost ->
    writer=actor) ->
  forall group,LeanCage_Entry_CallerPhysical_Tick_action tick<>
    LeanCage_Entry_CallerPhysical_Action_placement group.
Proof.
  intros ALIASES CLOSE ZERO RUN TABLE RECORDED WRITER group PLACED.
  destruct(RECORDED group PLACED)as[writer[fd[binding[object[bytes[lost[SOCKET[PRESENT[OBJECT CGROUP]]]]]]]]].
  specialize(WRITER _ _ _ _ SOCKET);subst writer;rewrite TABLE in PRESENT.
  pose proof(actual_closed_cgroup_stays_absent _ _ _ _ _ _ object
    (ALIASES _ _ CGROUP)CLOSE ZERO RUN)as ABSENT.
  eapply ABSENT;eassumption.
Qed.

Theorem actual_close_forbids_source_placement groups before descriptor reply closed events at_write
    runs tick run program ordinal event io group :
  cgroup_unique_aliases groups(namespace_table before)descriptor ->
  namespace_kernel_event before
    (namespace_process(process_entry(entry_library(close_returned descriptor reply))))closed ->
  close_value reply=Int.zero ->namespace_kernel_steps closed events at_write ->
  nth_error runs program=Some run ->nth_error(source_events run)ordinal=Some event ->
  namespace_socket_io event=Some io ->IO.operation(source_socket_request io)=IO.writing ->
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote(source_actor run)
    (caller_request_nat(IO.descriptor(source_socket_request io)))
    (journal_byte_values(source_socket_bytes io))(journal_lost_value(source_socket_lost io)) ->
  (forall fd,physical_tick_table tick
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run)))fd=namespace_table at_write fd) ->
  PlacementRecording groups tick ->
  LeanCage_Entry_CallerPhysical_Tick_action tick<>
    LeanCage_Entry_CallerPhysical_Action_placement group.
Proof.
  intros ALIASES CLOSE ZERO RUN PROGRAM EVENT IO WRITING SOCKET TABLE RECORDED.
  eapply actual_close_forbids_recorded_parent_placement;[exact ALIASES|exact CLOSE|exact ZERO|exact RUN|
    exact TABLE|exact RECORDED|].
  intros writer fd bytes lost SAME;rewrite SOCKET in SAME;inversion SAME;reflexivity.
Qed.
