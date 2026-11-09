(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Project actual C I/O bytes while retaining every operation position. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessStructure ProcessAllocation ProcessPaths
  ProcessReleaseSafety ProcessReleaseBytes.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceChannel NamespaceEndpoint.
Import ListNotations.
Open Scope Z_scope.

Record SourceSocketIO := {
  source_socket_request:request;
  source_socket_bytes:list Byte.int;
  source_socket_lost:bool
}.

Definition process_socket_io event:option SourceSocketIO:=match event with
  |process_entry(entry_library(original_event(io_step q(transfer bytes _))))=>
    Some{|source_socket_request:=q;source_socket_bytes:=bytes;source_socket_lost:=false|}
  |process_entry(entry_library(original_event(partial_loss q bytes _)))=>
    Some{|source_socket_request:=q;source_socket_bytes:=bytes;source_socket_lost:=true|}
  |_=>None end.

Definition namespace_socket_io event:=match event with
  |namespace_process original=>process_socket_io original|_=>None end.

Definition source_socket_projection(tables:nat->DescriptorTable)actor channel io:=
  let q:=source_socket_request io in
  match tables actor(descriptor q)with
  |None=>channel_passed
  |Some binding=>match descriptor_object binding with
    |ordinary_object _=>channel_passed
    |release_endpoint actual side=>if Nat.eqb actual channel then
      match operation q with
      |writing=>channel_sent actor(descriptor q)(source_socket_bytes io)(source_socket_lost io)
      |reading=>channel_read actor(descriptor q)(Z.to_nat(requested q))(source_socket_bytes io)
      end else channel_passed end end.

Definition namespace_socket_projection tables actor channel event:=
  match namespace_socket_io event with
  |Some io=>source_socket_projection tables actor channel io
  |None=>channel_passed end.

Theorem source_socket_send_has_actual_arguments tables actor channel io sender fd bytes lost:
  source_socket_projection tables actor channel io=channel_sent sender fd bytes lost ->
  sender=actor /\operation(source_socket_request io)=writing /\
    fd=descriptor(source_socket_request io) /\bytes=source_socket_bytes io /\lost=source_socket_lost io /\
    exists side binding,tables actor fd=Some binding /\
      descriptor_object binding=release_endpoint channel side.
Proof.
  unfold source_socket_projection.
  destruct(tables actor(descriptor(source_socket_request io)))as[binding|]eqn:PRESENT;[|discriminate].
  destruct(descriptor_object binding)as[ordinary|actual side]eqn:OBJECT;[discriminate|].
  destruct(Nat.eqb actual channel)eqn:CHANNEL;[|discriminate].
  apply Nat.eqb_eq in CHANNEL;subst actual.
  destruct(operation(source_socket_request io))eqn:OPERATION;[discriminate|].
  intro SAME;inversion SAME;subst;repeat split;try reflexivity;try assumption.
  exists side,binding;auto.
Qed.

Lemma process_socket_io_transports event io:
  process_socket_io event=Some io ->process_transports event=true.
Proof.
  unfold process_socket_io,process_transports.
  repeat match goal with
  |e:process_event|-_=>destruct e;try discriminate
  |e:entry_handoff_event|-_=>destruct e;try discriminate
  |e:library_event|-_=>destruct e;try discriminate
  |e:Machine.event|-_=>destruct e;try discriminate
  |r:reply|-_=>destruct r;try discriminate
  end;reflexivity.
Qed.

Theorem release_socket_io_exact peer event io:
  release_wire_event peer event ->process_socket_io event=Some io ->
  operation(source_socket_request io)=writing /\descriptor(source_socket_request io)=peer /\
    requested(source_socket_request io)=1 /\source_socket_bytes io=[Byte.repr 165].
Proof.
  intros WIRE SOURCE;unfold process_socket_io in SOURCE;unfold release_wire_event in WIRE.
  repeat match goal with
  |e:process_event|-_=>destruct e;cbn in SOURCE,WIRE;try discriminate
  |e:entry_handoff_event|-_=>destruct e;cbn in SOURCE,WIRE;try discriminate
  |e:library_event|-_=>destruct e;cbn in SOURCE,WIRE;try discriminate
  |e:Machine.event|-_=>destruct e;cbn in SOURCE,WIRE;try discriminate
  |r:reply|-_=>destruct r;cbn in SOURCE,WIRE;try discriminate
  end;inversion SOURCE;subst;cbn in *.
  - destruct WIRE as[OP[FD[COUNT BYTES]]];repeat split;try assumption.
    eapply BYTES;reflexivity.
  - exact WIRE.
Qed.

(* The helper prefix is supplied by the wider namespace call decomposition;
   this theorem uses its exact operation, even when acknowledgement is lost. *)
Theorem actual_release_socket_has_checked_resume_from_live_tls cell before child peer events target prefix event suffix io:
  Mem.valid_block before(tls_block cell) ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events target ->
  events=prefix++event::suffix ->process_socket_io event=Some io ->
  In(release_resume_event child)prefix /\
    operation(source_socket_request io)=writing /\descriptor(source_socket_request io)=peer /\
    requested(source_socket_request io)=1 /\source_socket_bytes io=[Byte.repr 165].
Proof.
  intros READY RUN EVENTS SOURCE;split.
  - eapply release_transport_requires_checked_resume;[exact RUN|exact EVENTS|].
    eapply process_socket_io_transports;exact SOURCE.
  - eapply release_socket_io_exact;[|exact SOURCE].
    pose proof(release_actual_wire_bytes_from_live_tls _ _ _ _ _ _ READY RUN)as WIRE.
    rewrite Forall_forall in WIRE;apply WIRE;rewrite EVENTS;apply in_or_app;right;left;reflexivity.
Qed.

Theorem actual_release_socket_has_checked_resume cell before child peer events target prefix event suffix io:
  entry_errno_ready cell before ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events target ->
  events=prefix++event::suffix ->process_socket_io event=Some io ->
  In(release_resume_event child)prefix /\
    operation(source_socket_request io)=writing /\descriptor(source_socket_request io)=peer /\
    requested(source_socket_request io)=1 /\source_socket_bytes io=[Byte.repr 165].
Proof.
  intros READY RUN EVENTS SOURCE;split.
  - eapply release_transport_requires_checked_resume;[exact RUN|exact EVENTS|].
    eapply process_socket_io_transports;exact SOURCE.
  - eapply release_socket_io_exact;[|exact SOURCE].
    pose proof(release_actual_wire_bytes _ _ _ _ _ _ READY RUN)as WIRE.
    rewrite Forall_forall in WIRE;apply WIRE;rewrite EVENTS;apply in_or_app;right;left;reflexivity.
Qed.
